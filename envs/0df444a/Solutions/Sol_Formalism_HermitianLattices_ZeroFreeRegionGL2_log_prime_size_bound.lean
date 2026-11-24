-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.log_prime_size_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:43.951814+00:00
-- url     : https://prove2.me/submissions/72f10628-3815-4908-b45a-6c6da0434971

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NormOneEstimateOfHypothesis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : Formalism.HermitianLattices.ZeroFreeRegionGL2.LogPrimeSizeBound := by
  intro ε C' hε hC'
  refine ⟨max 1 ((50 * C' / ε ^ 2) ^ (5 / (2 * ε))), ?_⟩
  intro x hx NE p hNE hp hlog hpN
  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (50 * C' / ε ^ 2) ^ (5 / (2 * ε)) ≤ x := le_trans (le_max_right _ _) hx
  have hNE0 : (0 : ℝ) < NE := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := Real.log_le_log hp hpN
    rwa [Real.log_rpow hNE0] at this
  · have := mul_le_mul_of_nonneg_left hlog hC'.le
    calc C' * Real.log NE ≤ C' * (2 * x ^ (ε / 5) * Real.log x ^ 2) := this
      _ = 2 * C' * x ^ (ε / 5) * Real.log x ^ 2 := by ring
  · have hK : (0 : ℝ) < 50 * C' / ε ^ 2 := by positivity
    have h1 : Real.log x ≤ x ^ (ε / 5) / (ε / 5) := Real.log_le_rpow_div hx0.le (by positivity)
    have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h2 : Real.log x ^ 2 ≤ (x ^ (ε / 5) / (ε / 5)) ^ 2 := pow_le_pow_left₀ hl0 h1 2
    have h3 : 50 * C' / ε ^ 2 ≤ x ^ (2 * ε / 5) := by
      have := Real.rpow_le_rpow (by positivity) hx2 (show (0 : ℝ) ≤ 2 * ε / 5 by positivity)
      rw [← Real.rpow_mul hK.le] at this
      have e : 5 / (2 * ε) * (2 * ε / 5) = 1 := by field_simp
      rwa [e, Real.rpow_one] at this
    set u := x ^ (ε / 5) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hx0 _
    have e2 : x ^ (2 * ε / 5) = u ^ 2 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    have e5 : x ^ ε = u ^ 5 := by
      rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
    rw [e5]
    rw [e2] at h3
    calc 2 * C' * u * Real.log x ^ 2 ≤ 2 * C' * u * (u / (ε / 5)) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (50 * C' / ε ^ 2) * u ^ 3 := by field_simp; ring
      _ ≤ u ^ 2 * u ^ 3 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = u ^ 5 := by ring
end Formalism.HermitianLattices.ZeroFreeRegionGL2
