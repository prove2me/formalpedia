-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integral_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:35.459803+00:00
-- url     : https://prove2.me/submissions/fbef3907-884d-4d89-800c-d71952943261

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution (m : ℤ) :
    ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2), Complex.exp (2 * π * Complex.I * (((m : ℝ) : ℂ) * (t : ℂ))) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  by_cases hm : m = 0
  · simp [hm]; norm_num
  · rw [if_neg hm]
    have hc : (2 * π * Complex.I * ((m : ℝ) : ℂ)) ≠ 0 := by
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hm, hpi]
    simp_rw [← mul_assoc]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * ((m : ℝ) : ℂ) * ((-(1 / 2) : ℝ) : ℂ)) := by
      rw [Complex.exp_eq_exp_iff_exists_int]
      refine ⟨m, ?_⟩
      push_cast
      ring
    rw [this, sub_self, zero_div]
end Formalism.FourierDecayAlt.P.HLsc
