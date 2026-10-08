-- Prove2me | solution 1 for ConnesRZ.mellinHat_conv_starInv_pair
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T15:02:15.879481+00:00
-- url     : https://prove2.me/submissions/1f3edc22-d223-483a-88fa-5e00b9e99508

import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_ExplicitFormula
set_option autoImplicit false
open Complex MeasureTheory Set Filter
open scoped ComplexConjugate Convolution
noncomputable section
namespace Zeta23.EF
theorem cintegral_const_mul (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f
theorem cintegral_mul_const (c : ℂ) (f : ℝ → ℂ) : ∫ x, f x * c = (∫ x, f x) * c :=
  integral_mul_const c f
theorem cintegral_conj (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj

/-! ## Dictionary with Mathlib's Fourier transform -/

/-- `h_k(τ) = 𝓕 k (−τ/(2π))` for real τ. -/
theorem continuous_tilde {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)
theorem hasCompactSupport_tilde {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)
theorem paperFT_tilde (g : ℝ → ℂ) (z : ℂ) :
    paperFT (tilde g) z = conj (paperFT g (conj z)) := by
  unfold paperFT tilde
  rw [← cintegral_conj, ← integral_neg_eq_self]
  congr 1; ext u
  simp only [map_mul, ← Complex.exp_conj, conj_conj, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_neg]
  ring_nf

/-- App. A: `h_{f⋆g̃}(z) = h_f(z) · conj(h_g(conj z))` for all complex z. -/
theorem paperFT_weilTest {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (z : ℂ) :
    paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) := by
  rw [← paperFT_tilde]
  have hgt : Continuous (tilde g) := continuous_tilde hg
  have hgts : HasCompactSupport (tilde g) := hasCompactSupport_tilde hgs
  -- the integrand on ℝ × ℝ : (x,t) ↦ f(t) g̃(x−t) e^{izx}, continuous with compact support
  have hFc : Continuous (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    change Continuous fun p : ℝ × ℝ => f p.2 * tilde g (p.1 - p.2) * cexp (I * z * p.1)
    fun_prop
  have hFs : HasCompactSupport
      (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    refine HasCompactSupport.intro ((hgts.isCompact.add hfs.isCompact).prod hfs.isCompact) ?_
    rintro ⟨x, t⟩ hxt
    change f t * tilde g (x - t) * cexp (I * z * x) = 0
    rw [mem_prod, not_and_or] at hxt
    rcases hxt with hx | ht
    · by_cases ht : t ∈ tsupport f
      · have hx' : x - t ∉ tsupport (tilde g) := fun h => hx ⟨x - t, h, t, ht, by ring⟩
        rw [image_eq_zero_of_notMem_tsupport hx']; simp
      · rw [image_eq_zero_of_notMem_tsupport ht]; simp
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  have hFi : Integrable (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x))
      (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  -- translation v = x − t in the inner integral
  have hshift : ∀ t : ℝ, ∫ x : ℝ, tilde g (x - t) * cexp (I * z * x)
      = cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
    intro t
    rw [← cintegral_const_mul,
      ← integral_sub_right_eq_self (fun v : ℝ => cexp (I * z * t) * (tilde g v * cexp (I * z * v))) t]
    congr 1; ext x
    simp only [Complex.ofReal_sub]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  calc paperFT (weilTest f g) z
      = ∫ x : ℝ, (∫ t : ℝ, f t * tilde g (x - t)) * cexp (I * z * x) := by
        simp only [paperFT, weilTest, convolution_def, ContinuousLinearMap.mul_apply']
    _ = ∫ x : ℝ, ∫ t : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := by
        congr 1; ext x; rw [← cintegral_mul_const]
    _ = ∫ t : ℝ, ∫ x : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := integral_integral_swap hFi
    _ = ∫ t : ℝ, f t * cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
        congr 1; ext t
        rw [show (fun x : ℝ => f t * tilde g (x - t) * cexp (I * z * x))
            = fun x => f t * (tilde g (x - t) * cexp (I * z * x)) from funext fun _ => mul_assoc _ _ _,
          cintegral_const_mul, hshift t]
        ring
    _ = paperFT f z * paperFT (tilde g) z := by
        simp only [paperFT]; rw [← cintegral_mul_const]

end Zeta23.EF
namespace ConnesRZArithmetic
lemma connes_paperFT_dictionary (g : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT g z = ConnesRZ.mellinHat g (1 / 2 + I * z) := by
  unfold Zeta23.paperFT ConnesRZ.mellinHat
  congr 1
  funext t
  congr 1
  congr 1
  ring
lemma connes_paperFT_at_zero (g : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT g (Zeta23.gammaOf s) = ConnesRZ.mellinHat g s := by
  rw [connes_paperFT_dictionary]
  congr 1
  unfold Zeta23.gammaOf
  field_simp
  ring
lemma conv_starInv_eq_weilTest (f g : ℝ → ℂ) :
    ConnesRZ.conv f (ConnesRZ.starInv g) = Zeta23.EF.weilTest f g := by
  funext t
  rfl
lemma gammaOf_reflect_eq_conj (s : ℂ) :
    Zeta23.gammaOf (1 - (starRingEnd ℂ) s) =
      (starRingEnd ℂ) (Zeta23.gammaOf s) := by
  unfold Zeta23.gammaOf
  simp only [map_div₀, map_sub, map_one, map_ofNat, Complex.conj_I]
  field_simp
  ring
lemma paperFT_conj_gamma_eq_mellinHat (g : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT g ((starRingEnd ℂ) (Zeta23.gammaOf s)) =
      ConnesRZ.mellinHat g (1 - (starRingEnd ℂ) s) := by
  rw [← gammaOf_reflect_eq_conj, connes_paperFT_at_zero]

end ConnesRZArithmetic
open ConnesRZ
theorem solution (f g : ℝ → ℂ) (hf : Continuous f)
    (hg : Continuous g) (hfs : HasCompactSupport f) (hgs : HasCompactSupport g)
    (s : ℂ) :
    mellinHat (conv f (starInv g)) s =
      mellinHat f s * (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) s)) := by
  rw [← ConnesRZArithmetic.connes_paperFT_at_zero,
    ConnesRZArithmetic.conv_starInv_eq_weilTest,
    Zeta23.EF.paperFT_weilTest hf hg hfs hgs,
    ConnesRZArithmetic.connes_paperFT_at_zero,
    ConnesRZArithmetic.paperFT_conj_gamma_eq_mellinHat]
