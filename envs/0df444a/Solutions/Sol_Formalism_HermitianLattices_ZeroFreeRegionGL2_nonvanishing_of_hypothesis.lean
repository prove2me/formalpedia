-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.nonvanishing_of_hypothesis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:10.10925+00:00
-- url     : https://prove2.me/submissions/38ccaada-36ad-455f-ba13-9e9b02d23098

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CharacterEstimateOfHypothesis
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_numerical_nonvanishing_bound
import Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_gl2b2_thinIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
private lemma gl2b2_big_lemma {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → M ≤ x ^ a := by
  refine ⟨max 1 (|M| ^ (1 / a)), le_max_left _ _, fun x hx => ?_⟩
  have h2 : |M| ^ (1 / a) ≤ x := le_trans (le_max_right _ _) hx
  have h3 : (|M| ^ (1 / a)) ^ a ≤ x ^ a :=
    Real.rpow_le_rpow (by positivity) h2 ha.le
  rw [← Real.rpow_mul (abs_nonneg M), one_div_mul_cancel ha.ne', Real.rpow_one] at h3
  exact le_trans (le_abs_self M) h3
end Formalism.HermitianLattices.ZeroFreeRegionGL2
end

set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound := by
  unfold Formalism.HermitianLattices.ZeroFreeRegionGL2.TailIntegralBoundOfPsiBound
  intro ε c C hε hc hC
  obtain ⟨c0, X0, hc0, hX0⟩ := gl2b2_thinIntegral ε c hε hc
  obtain ⟨XN, hXN⟩ := numerical_nonvanishing_bound ε hε
  obtain ⟨XW, -, hXW⟩ := gl2b2_big_lemma (a := ε / 8) (by positivity) (2 * C / c0)
  refine ⟨c0 / 2, max (max X0 XN) XW, by positivity, ?_⟩
  intro x hx y lam psi0 hy hlam1 hlam hpsi
  have hxX0 : X0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxN : XN ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxW : XW ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hV, -, -⟩ := hXN x hxN y lam hy (by linarith) hlam
  obtain ⟨hGint, hGle⟩ := hX0 x hxX0 (Real.log y) lam hV hlam1 hlam
  have hypos : 0 < y := lt_of_lt_of_le (by positivity) hy
  set G : ℝ → ℝ := fun v => (v + lam) ^ 2 * Real.exp (-c * v / (lam + Real.sqrt v)) with hGdef
  have himg : Real.log '' Set.Ioi y = Set.Ioi (Real.log y) := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact Real.log_lt_log hypos hu
    · intro hv
      refine ⟨Real.exp v, ?_, Real.log_exp v⟩
      have h1 : Real.exp (Real.log y) < Real.exp v := Real.exp_lt_exp.mpr hv
      rwa [Real.exp_log hypos] at h1
  have hderiv : ∀ u ∈ Set.Ioi y, HasDerivWithinAt Real.log u⁻¹ (Set.Ioi y) u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    exact (Real.hasDerivAt_log hu0.ne').hasDerivWithinAt
  have hinj : Set.InjOn Real.log (Set.Ioi y) :=
    Real.log_injOn_pos.mono (Set.Ioi_subset_Ioi hypos.le)
  have hHint : MeasureTheory.IntegrableOn (fun u : ℝ => |u⁻¹| • G (Real.log u)) (Set.Ioi y) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G).mp (by rw [himg]; exact hGint)
  have hHeq : (∫ u in Set.Ioi y, |u⁻¹| • G (Real.log u)) = ∫ v in Set.Ioi (Real.log y), G v := by
    have h1 := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
      hinj G
    rw [himg] at h1
    exact h1.symm
  have hbound : ∀ u ∈ Set.Ioi y, ‖psi0 u / (u : ℂ) ^ 2‖ ≤ C * (|u⁻¹| • G (Real.log u)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hypos hu
    have hu0' : u ≠ 0 := hu0.ne'
    have h1 := hpsi u (le_of_lt hu)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0,
      abs_of_pos (inv_pos.mpr hu0), smul_eq_mul, div_le_iff₀ (by positivity)]
    have hG : G (Real.log u) = (Real.log u + lam) ^ 2 *
        Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := rfl
    have hu2 : u⁻¹ * u ^ 2 = u := by
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hu0', one_mul]
    rw [hG]
    calc ‖psi0 u‖ ≤ C * u * (Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))) := h1
      _ = C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 := by
        rw [show C * (u⁻¹ * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u))))) * u ^ 2 =
          C * ((Real.log u + lam) ^ 2 *
          Real.exp (-c * Real.log u / (lam + Real.sqrt (Real.log u)))) * (u⁻¹ * u ^ 2) by ring,
          hu2]
        ring
  have hnorm : ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤
      ∫ u in Set.Ioi y, C * (|u⁻¹| • G (Real.log u)) :=
    MeasureTheory.norm_integral_le_of_norm_le (hHint.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hbound)
  rw [MeasureTheory.integral_const_mul, hHeq] at hnorm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hypos]
  refine mul_le_mul_of_nonneg_left ?_ hypos.le
  have hw := hXW x hxW
  have hCexp : C ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) := by
    have h1 := Real.add_one_le_exp (c0 / 2 * x ^ (ε / 8))
    rw [div_le_iff₀ hc0] at hw
    linarith
  calc ‖∫ u in Set.Ioi y, psi0 u / (u : ℂ) ^ 2‖ ≤ C * ∫ v in Set.Ioi (Real.log y), G v := hnorm
    _ ≤ C * Real.exp (-c0 * x ^ (ε / 8)) := mul_le_mul_of_nonneg_left hGle hC.le
    _ ≤ Real.exp (c0 / 2 * x ^ (ε / 8)) * Real.exp (-c0 * x ^ (ε / 8)) :=
        mul_le_mul_of_nonneg_right hCexp (Real.exp_pos _).le
    _ = Real.exp (-(c0 / 2) * x ^ (ε / 8)) := by rw [← Real.exp_add]; congr 1; ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
