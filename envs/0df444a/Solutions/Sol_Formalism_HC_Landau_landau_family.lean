-- Prove2me | solution 1 for Formalism.HC.Landau.landau_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:30.813795+00:00
-- url     : https://prove2.me/submissions/ed443f82-7614-4378-abed-1cc64530c1a6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Landau
import Theorems.Thm_Formalism_HC_Landau_landau_entire
import Theorems.Thm_Formalism_HC_Landau_lseries_re
import Theorems.Thm_P2M_Formalism_HC_Landau_mellin_Gchi__2c78370e3378
import Theorems.Thm_Formalism_HC_Landau_lseries_real_im
import Theorems.Thm_Formalism_HC_Landau_Gchi_bdd
import Theorems.Thm_Formalism_Gz_bdd
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_cint_of_abs
import Theorems.Thm_Formalism_differentiable_deriv_of
import Theorems.Thm_Formalism_int_abs_rpow
import Theorems.Thm_Formalism_landauIteratedDerivatives_key
import Theorems.Thm_Formalism_measurable_Gchi
import Theorems.Thm_Formalism_measurable_Gz
import Theorems.Thm_Formalism_mellinElem
import Theorems.Thm_Formalism_mellinSgen
import Theorems.Thm_Formalism_mellin_Gz
import Theorems.Thm_Formalism_mellin_Gz_n
import Theorems.Thm_Formalism_ne_one_of_one_lt_re
import Theorems.Thm_Formalism_ne_zero_of_lt_re
import Theorems.Thm_Formalism_riemannZetaOne_eq_mul_of_ne_one
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_one_le_re
import Theorems.Thm_Formalism_rint_Gchi
import Theorems.Thm_Formalism_rint_Gz
import Theorems.Thm_Formalism_sub_ne_zero_of_lt_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism Formalism.HC Formalism.HC.Landau
open Formalism ArithmeticFunction
open DirichletCharacter
variable {N : ℕ} [NeZero N]
set_option maxHeartbeats 1000000
namespace Formalism.HC.Landau
theorem _root_.solution {ι : Type} (c : ι → PChar) (τ : ι → ι) (hτ : ∀ i, τ (τ i) = i) (hτc : ∀ i, c (τ i) = (c i).inv)
    (S : Finset ι) (h1 : ∀ ξ ∈ S, (c ξ).χ ≠ 1) (hinv : ∀ ξ ∈ S, τ ξ ∈ S) (R : ℕ) (hR : R ≠ 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (C0 y0 : ℝ) (hb : ∀ y ≥ y0, R * Gz y + ∑ ξ ∈ S, Gchi (c ξ).χ y ≤ C0 * y ^ θ) :
    ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0 ∧ ∀ ξ ∈ S, LFunction (c ξ).χ s ≠ 0 := by
  classical
  have h3 := mellinSgen
  have h5 := mellinElem
  have hLd : ∀ ξ ∈ S, Differentiable ℂ (LFunction (c ξ).χ) := fun ξ h => differentiable_LFunction (h1 ξ h)
  have hL1 : ∀ s : ℂ, 1 ≤ s.re → ∀ ξ ∈ S, LFunction (c ξ).χ s ≠ 0 :=
    fun s hs ξ h => LFunction_ne_zero_of_one_le_re (c ξ).χ (Or.inl (h1 ξ h)) hs
  set P : ℂ → ℂ := fun s => riemannZeta₁ s ^ R * ∏ ξ ∈ S, LFunction (c ξ).χ s with hPdef
  have hZd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hPr : Differentiable ℂ fun s => ∏ ξ ∈ S, LFunction (c ξ).χ s :=
    fun s => DifferentiableAt.fun_finsetProd fun ξ h => hLd ξ h s
  have hP : Differentiable ℂ P := (hZd.pow R).mul hPr
  have hP1 : ∀ s : ℂ, 1 ≤ s.re → P s ≠ 0 := fun s hs =>
    mul_ne_zero (pow_ne_zero _ (riemannZetaOne_ne_zero_of_one_le_re hs)) (Finset.prod_ne_zero_iff.2 (hL1 s hs))
  set g : ℂ → ℂ := fun s => ∑ ξ ∈ S, deriv (LFunction (c ξ).χ) s / LFunction (c ξ).χ s with hg
  have hlog : ∀ s : ℂ, 1 ≤ s.re → deriv P s / P s = R * (deriv riemannZeta₁ s / riemannZeta₁ s) + g s := by
    intro s hs
    have e := logDeriv_mul (f := fun s => riemannZeta₁ s ^ R) (g := fun s => ∏ ξ ∈ S, LFunction (c ξ).χ s) s
      (pow_ne_zero _ (riemannZetaOne_ne_zero_of_one_le_re hs)) (Finset.prod_ne_zero_iff.2 (hL1 s hs)) ((hZd.pow R) s) (hPr s)
    rw [logDeriv_fun_pow (hZd s), logDeriv_prod (hL1 s hs) (fun ξ h => hLd ξ h s)] at e
    simpa [logDeriv_apply] using e
  have hsumL : ∀ s : ℂ, 1 < s.re → ∑ ξ ∈ S, LSeries (fun n => ((Λ n * ((c ξ).χ n).re : ℝ) : ℂ)) s = -g s := by
    intro s hs
    have hi : ∑ ξ ∈ S, deriv (LFunction (c ξ).χ⁻¹) s / LFunction (c ξ).χ⁻¹ s = g s :=
      Finset.sum_bij' (fun ξ _ => τ ξ) (fun ξ _ => τ ξ) (fun ξ h => hinv ξ h) (fun ξ h => hinv ξ h)
        (fun ξ _ => hτ ξ) (fun ξ _ => hτ ξ)
        (fun ξ _ => congrArg (fun ψ : PChar => deriv (LFunction ψ.χ) s / LFunction ψ.χ s) (hτc ξ).symm)
    rw [Finset.sum_congr rfl fun ξ _ => lseries_re (c ξ).χ hs, ← Finset.sum_div, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, hi]
    simp only [hg]
    ring
  have him : (g 1).im = 0 := by
    have hc : ContinuousAt g 1 := by
      refine tendsto_finsetSum _ fun ξ h => ?_
      exact ((differentiable_deriv_of (hLd ξ h)).continuous.tendsto 1).div ((hLd ξ h).continuous.tendsto 1)
        (hL1 1 (by simp) ξ h)
    have hp : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] 1) (𝓝 1) := by
      have := (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
      simpa using this
    have ht := (Complex.continuous_im.tendsto _).comp (hc.tendsto.comp hp)
    have hz : ∀ᶠ σ : ℝ in 𝓝[>] 1, (im ∘ g ∘ fun σ : ℝ => (σ : ℂ)) σ = 0 := by
      refine eventually_nhdsWithin_of_forall fun σ hσ => ?_
      have e := congrArg Complex.im (hsumL σ (by simpa using hσ))
      rw [im_sum, Finset.sum_eq_zero fun ξ _ => lseries_real_im _ σ, neg_im] at e
      simp only [Function.comp_apply]
      linarith
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (hz.mono fun _ h => h.symm))
  have hre : ∑ ξ ∈ S, (((deriv (LFunction (c ξ).χ) 1 / LFunction (c ξ).χ 1).re : ℝ) : ℂ) = g 1 := by
    rw [← ofReal_sum, ← re_sum]
    apply Complex.ext
    · simp [hg]
    · rw [him, ofReal_im]

  obtain ⟨B, hB0, hB⟩ := Gz_bdd (le_max_right y0 1)
  choose B' hB'0 hB' using fun ξ : ι => Gchi_bdd (c ξ).χ (max y0 1)
  set C : ℝ := max C0 (R * B + ∑ ξ ∈ S, B' ξ) with hC
  set H : ℝ → ℝ := fun x => C * x ^ θ - (R * Gz x + ∑ ξ ∈ S, Gchi (c ξ).χ x) with hHdef
  have hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ H x := by
    intro x hx
    have hxθ : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ0.le
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    have hB2 : 0 ≤ R * B + ∑ ξ ∈ S, B' ξ := add_nonneg (mul_nonneg hR0 hB0) (Finset.sum_nonneg fun ξ _ => hB'0 ξ)
    have c1 : C0 ≤ C := le_max_left _ _
    have c2 : R * B + ∑ ξ ∈ S, B' ξ ≤ C := le_max_right _ _
    simp only [hHdef]
    rcases le_or_gt x (max y0 1) with hxX | hxX
    · have a1 : R * Gz x ≤ R * B := mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB x hx hxX)) hR0
      have a2 : ∑ ξ ∈ S, Gchi (c ξ).χ x ≤ ∑ ξ ∈ S, B' ξ :=
        Finset.sum_le_sum fun ξ _ => (le_abs_self _).trans (hB' ξ x hx hxX)
      exact sub_nonneg.2 ((add_le_add a1 a2).trans (c2.trans (le_mul_of_one_le_right (hB2.trans c2) hxθ)))
    · have a1 := hb x (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hxX))
      have a2 : C0 * x ^ θ ≤ C * x ^ θ := mul_le_mul_of_nonneg_right c1 (zero_le_one.trans hxθ)
      exact sub_nonneg.2 (a1.trans a2)
  have hm : Measurable H := by
    have a1 := measurable_Gz h3
    have a2 : Measurable fun x => ∑ ξ ∈ S, Gchi (c ξ).χ x := Finset.measurable_fun_sum _ fun ξ _ => measurable_Gchi h3 (c ξ).χ
    exact (measurable_const.mul (measurable_id.pow_const _)).sub ((measurable_const.mul a1).add a2)
  have hI : ∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => H x * x ^ (-σ - 1)) (Ioi 1) := by
    intro σ hσ
    have hfun : (fun x : ℝ => H x * x ^ (-σ - 1)) = fun x =>
        C * (x ^ θ * x ^ (-σ - 1)) - (R * (Gz x * x ^ (-σ - 1)) + ∑ ξ ∈ S, Gchi (c ξ).χ x * x ^ (-σ - 1)) := by
      funext x
      simp only [hHdef]
      rw [← Finset.sum_mul]
      ring
    rw [hfun]
    exact Integrable.sub (Integrable.const_mul (h5.1 θ σ (by linarith)) _)
      (Integrable.add (Integrable.const_mul (rint_Gz h3 h5 hσ) _)
        (integrable_finsetSum _ fun ξ _ => rint_Gchi h3 h5 (c ξ).χ hσ))
  have hA : AP P (-R) (R * (1 + (Real.eulerMascheroniConstant : ℂ)) + g 1) 1 = 0 := by
    have e := hlog 1 (by simp)
    have hp := hP1 1 (by simp)
    rw [deriv_riemannZeta₁_one, riemannZeta₁_one, div_eq_iff hp] at e
    unfold AP
    rw [e]
    ring
  have key := landau_entire P hP hP1 _ _ hA H hm hH hI C θ hθ0 hθ1 (by
    intro s hs
    have iz := (mellin_Gz h3 h5 hs).1
    have i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
      cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
    have iS : Integrable (fun x : ℝ => ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi 1)) :=
      integrable_finsetSum _ fun ξ _ => (mellin_Gchi' (c ξ).χ hs).1
    have hfun : (fun x : ℝ => ((H x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
        (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) -
          ((R : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) + ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      funext x
      simp only [hHdef]
      rw [← Finset.sum_mul]
      push_cast
      ring
    have j1 := Integrable.const_mul iz (R : ℂ)
    have j2 : Integrable (fun x : ℝ => (R : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1)) +
        ∑ ξ ∈ S, (Gchi (c ξ).χ x : ℂ) * (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi 1)) := j1.add iS
    rw [hfun, integral_sub (Integrable.const_mul i4 _) j2, integral_add j1 iS, integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun ξ _ => (mellin_Gchi' (c ξ).χ hs).1, Finset.sum_congr rfl fun ξ _ => (mellin_Gchi' (c ξ).χ hs).2,
      Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, hsumL s hs, hre, mellin_Gz_n h3 h5 hs,
      h5.2.2.1 θ s (by linarith), hlog s hs.le]
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hs)
    have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
    have hsθ : s - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    unfold nZ linZ
    generalize deriv riemannZeta₁ s / riemannZeta₁ s = u
    field_simp
    ring)
  intro s hs
  have hne := key s hs
  have hZ1 : riemannZeta₁ s ≠ 0 := fun h => hne (by simp [hPdef, h, hR])
  refine ⟨?_, Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hne)⟩
  by_cases h1 : s = 1
  · subst h1
    exact riemannZeta_ne_zero_of_one_le_re (by simp)
  · rw [riemannZetaOne_eq_mul_of_ne_one h1] at hZ1
    exact right_ne_zero_of_mul hZ1
end Formalism.HC.Landau
