-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.tendsto_phaseUnitary
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:07:11.251196+00:00
-- url     : https://prove2.me/submissions/0c47be5c-db8b-4cc3-bc25-34a7315075eb

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNsLagrangianDetConvolution

open scoped ENNReal InnerProductSpace

namespace A76d46d9Aux

open BookProof.ChapterContinuityUnitaryInfinite BookProof.ChapterUnboundedPosition in
theorem norm_sq_sub (f : ℤ → ℝ) (t : ℝ) (psi : L2Z) :
    ‖(phaseUnitary f t psi : L2Z) - psi‖ ^ 2
      = ∑' k : ℤ, ‖(phase f t k - 1) * (psi : ℤ → ℂ) k‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  refine tsum_congr fun k => ?_
  congr 2
  rw [lp.coeFn_sub, Pi.sub_apply]
  show phase f t k * (psi : ℤ → ℂ) k - (psi : ℤ → ℂ) k = _
  ring

open BookProof.ChapterContinuityUnitaryInfinite BookProof.ChapterUnboundedPosition in
theorem tendsto_sq (f : ℤ → ℝ) (psi : L2Z) :
    Filter.Tendsto (fun t : ℝ => ∑' k : ℤ, ‖(phase f t k - 1) * (psi : ℤ → ℂ) k‖ ^ 2)
      (nhds 0) (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := nhds (0:ℝ))
    (f := fun t k => ‖(phase f t k - 1) * (psi : ℤ → ℂ) k‖ ^ 2)
    (g := fun _ => (0:ℝ)) (bound := fun k => 4 * ‖(psi : ℤ → ℂ) k‖ ^ 2)
    ((summable_normSq psi).mul_left 4) ?_ ?_
  · simpa using h
  · intro k
    have hc : Continuous fun t : ℝ => ‖(phase f t k - 1) * (psi : ℤ → ℂ) k‖ ^ 2 := by
      unfold phase; fun_prop
    have := hc.tendsto 0
    simpa [phase] using this
  · refine Filter.Eventually.of_forall fun t k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, mul_pow]
    have h1 : ‖phase f t k - 1‖ ≤ 2 := by
      calc ‖phase f t k - 1‖ ≤ ‖phase f t k‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_phase, norm_one]; norm_num
    have h2 : ‖phase f t k - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (phase f t k - 1)]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)

end A76d46d9Aux

open BookProof.ChapterContinuityUnitaryInfinite BookProof.NsLagrangianDet BookProof.ChapterUnboundedPosition in
theorem solution (f : ℤ → ℝ) (psi : L2Z) :
    Filter.Tendsto (fun t : ℝ => phaseUnitary f t psi) (nhds 0) (nhds psi) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (Real.continuous_sqrt.tendsto 0).comp (A76d46d9Aux.tendsto_sq f psi)
  rw [Real.sqrt_zero] at h
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, ← A76d46d9Aux.norm_sq_sub]
  exact Real.sqrt_sq (norm_nonneg _)
