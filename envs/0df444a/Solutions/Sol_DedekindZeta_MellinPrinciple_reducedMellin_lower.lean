-- Prove2me | solution 1 for DedekindZeta.MellinPrinciple.reducedMellin_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:29:22.125492+00:00
-- url     : https://prove2.me/submissions/34147ef7-8a54-4dc8-bebb-b2fc804dbb73

import Mathlib
import Definitions.Def_DedekindZeta_MellinPrinciple
import Theorems.Thm_DedekindZeta_MellinPrinciple_reducedMellin_convergent
import Theorems.Thm_DedekindZeta_MellinPrinciple_mellinTail_integrable_right

set_option autoImplicit true
open MeasureTheory Set Filter Asymptotics Topology Complex
open DedekindZeta DedekindZeta.MellinPrinciple
variable {f g : ℝ → ℂ} {a₀ b₀ C : ℂ} {k c α : ℝ}
namespace DedekindZeta.MellinPrinciple
theorem _root_.solution (h : IsMellinPair f g a₀ b₀ C k c α) {s : ℂ}
    (hs : k < s.re) :
    (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
      = -a₀ / s + C * b₀ / (s - (k : ℂ))
        + ∫ y in Ioi (1 : ℝ), C * (g y - b₀) * (y : ℂ) ^ ((k : ℂ) - s - 1) := by
  have hkpos := h.hk
  have hspos : 0 < s.re := lt_trans hkpos hs
  have hsne : s ≠ 0 := by
    intro h0; rw [h0, Complex.zero_re] at hspos; exact lt_irrefl _ hspos
  have hsk : s - (k : ℂ) ≠ 0 := by
    intro h0
    have : s = (k : ℂ) := by linear_combination h0
    rw [this, Complex.ofReal_re] at hs; exact lt_irrefl _ hs
  -- The substituted/tail cpow exponent has real part `< -1` since `k < s.re`.
  have hexp : ((k : ℂ) - s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith
  -- (1) `y ↦ y^(s-1)` is integrable on `Ioc 0 1` (`Re (s-1) > -1`).
  have hcpow_ioc : IntegrableOn (fun y : ℝ => (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    apply intervalIntegral.intervalIntegrable_cpow'
    simp only [Complex.sub_re, Complex.one_re]; linarith
  -- `(f - a₀)·y^(s-1)` is integrable on `Ioi 0` (Mellin convergence), hence on `Ioc 0 1`.
  have hconv := reducedMellin_convergent h hs
  have hfa_ioi : IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioi (0 : ℝ)) := by
    refine hconv.congr_fun ?_ measurableSet_Ioi
    intro y _; simp [smul_eq_mul, mul_comm]
  have hfa_ioc : IntegrableOn (fun y : ℝ => (f y - a₀) * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
    hfa_ioi.mono_set Ioc_subset_Ioi_self
  have ha0_ioc : IntegrableOn (fun y : ℝ => a₀ * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) :=
    hcpow_ioc.const_mul a₀
  have hf_ioc : IntegrableOn (fun y : ℝ => f y * (y : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) 1) := by
    refine (hfa_ioc.add ha0_ioc).congr_fun ?_ measurableSet_Ioc
    intro y _; simp only [Pi.add_apply]; ring
  -- (2) The constant-term boundary integral `∫_{Ioc 0 1} a₀ y^(s-1) = a₀/s`.
  have hconst : (∫ y in Ioc (0 : ℝ) 1, a₀ * (y : ℂ) ^ (s - 1)) = a₀ / s := by
    rw [integral_const_mul]
    have hcpow : (∫ y in Ioc (0 : ℝ) 1, (y : ℂ) ^ (s - 1)) = 1 / s := by
      rw [← intervalIntegral.integral_of_le zero_le_one,
        integral_cpow (Or.inl (by simp only [Complex.sub_re, Complex.one_re]; linarith))]
      rw [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow, Complex.ofReal_zero,
        Complex.zero_cpow hsne, sub_zero]
    rw [hcpow, mul_one_div]
  -- (3) The `y ↦ 1/y` substitution turns `∫_{Ioc 0 1} f y·y^(s-1)` into the `g`-integral.
  have hsubst : (∫ y in Ioc (0 : ℝ) 1, f y * (y : ℂ) ^ (s - 1))
      = ∫ u in Ioi (1 : ℝ), C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1) := by
    have himg : (fun y : ℝ => y⁻¹) '' (Ioc (0 : ℝ) 1) = Ici 1 := by
      ext z
      simp only [mem_image, mem_Ioc, mem_Ici]
      constructor
      · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
        exact (one_le_inv₀ hy0).mpr hy1
      · intro hz
        have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
        exact ⟨z⁻¹, ⟨inv_pos.mpr hz0, (inv_le_one₀ hz0).mpr hz⟩, inv_inv z⟩
    have hderiv : ∀ x ∈ Ioc (0 : ℝ) 1,
        HasDerivWithinAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) (Ioc (0 : ℝ) 1) x :=
      fun x hx => (hasDerivAt_inv (ne_of_gt hx.1)).hasDerivWithinAt
    have hinj : InjOn (fun y : ℝ => y⁻¹) (Ioc (0 : ℝ) 1) :=
      fun a _ b _ hab => inv_inj.mp hab
    have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hderiv hinj
      (fun u : ℝ => C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1))
    rw [himg, integral_Ici_eq_integral_Ioi] at key
    rw [key]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    obtain ⟨hx0, _⟩ := hx
    set X : ℂ := (x : ℂ) with hX
    have hXne : X ≠ 0 := by rw [hX]; exact_mod_cast ne_of_gt hx0
    have harg : X.arg ≠ Real.pi := by
      rw [hX, Complex.arg_ofReal_of_nonneg hx0.le]; exact (Real.pi_ne_zero).symm
    have hfe := h.hfe x⁻¹ (inv_pos.mpr hx0)
    rw [one_div, inv_inv] at hfe
    have hbase : ((x⁻¹ ^ k : ℝ) : ℂ) = (X⁻¹) ^ (k : ℂ) := by
      rw [Complex.ofReal_cpow (inv_nonneg.mpr hx0.le), Complex.ofReal_inv, hX]
    have hxsq : (((x ^ 2)⁻¹ : ℝ) : ℂ) = (X ^ 2)⁻¹ := by rw [hX]; push_cast; ring
    have hinvcast : ((x⁻¹ : ℝ) : ℂ) = X⁻¹ := by rw [hX]; exact Complex.ofReal_inv x
    have hX2 : (X ^ 2)⁻¹ = X ^ (-(2 : ℂ)) := by
      rw [Complex.cpow_neg]
      norm_num [Complex.cpow_natCast X 2]
    have cpid : (X⁻¹) ^ (k : ℂ) * X ^ (s - 1)
        = (X ^ 2)⁻¹ * (X⁻¹) ^ ((k : ℂ) - s - 1) := by
      rw [Complex.inv_cpow X _ harg, Complex.inv_cpow X _ harg,
        ← Complex.cpow_neg, ← Complex.cpow_neg, hX2,
        ← Complex.cpow_add _ _ hXne, ← Complex.cpow_add _ _ hXne]
      congr 1; ring
    rw [Complex.real_smul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (x ^ 2)⁻¹), hfe,
      hbase, hxsq, hinvcast]
    linear_combination (C * g x⁻¹) * cpid
  -- (4) Split `g u = (g u - b₀) + b₀`; the `b₀` part is the pole `C b₀/(s-k)`.
  have htail := mellinTail_integrable_right (h := h) (s := s)
  have hconstg : IntegrableOn
      (fun u : ℝ => C * b₀ * (u : ℂ) ^ ((k : ℂ) - s - 1)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_cpow_of_lt hexp one_pos).const_mul (C * b₀)
  have hsplit_g : (∫ u in Ioi (1 : ℝ), C * g u * (u : ℂ) ^ ((k : ℂ) - s - 1))
      = (∫ u in Ioi (1 : ℝ), C * (g u - b₀) * (u : ℂ) ^ ((k : ℂ) - s - 1))
        + C * b₀ / (s - (k : ℂ)) := by
    have hpole : (∫ u in Ioi (1 : ℝ), C * b₀ * (u : ℂ) ^ ((k : ℂ) - s - 1))
        = C * b₀ / (s - (k : ℂ)) := by
      rw [integral_const_mul, integral_Ioi_cpow_of_lt hexp one_pos]
      rw [sub_add_cancel, Complex.ofReal_one, Complex.one_cpow]
      have hks : (k : ℂ) - s ≠ 0 := sub_ne_zero.mpr (fun e => hsk (by linear_combination -e))
      field_simp
      ring
    rw [← hpole, ← integral_add htail hconstg]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    ring
  -- Assemble.
  have step1 : (∫ y in Ioc (0 : ℝ) 1, (f y - a₀) * (y : ℂ) ^ (s - 1))
      = (∫ y in Ioc (0 : ℝ) 1, f y * (y : ℂ) ^ (s - 1))
        - (∫ y in Ioc (0 : ℝ) 1, a₀ * (y : ℂ) ^ (s - 1)) := by
    rw [← integral_sub hf_ioc ha0_ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun y _ => ?_)
    ring
  rw [step1, hsubst, hconst, hsplit_g]
  ring
end DedekindZeta.MellinPrinciple
