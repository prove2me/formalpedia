-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz2.inv_pow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:38.340248+00:00
-- url     : https://prove2.me/submissions/0437504a-e0f5-47fd-a243-ffe7aff39936

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz2
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz2
theorem _root_.solution (q j : ℕ) (hq : 2 ≤ q) (hj : 1 ≤ j) :
    0 ≤ ((q : ℝ) ^ j)⁻¹ ∧ ((q : ℝ) ^ j)⁻¹ ≤ 1 / 2 ^ j ∧ (1 : ℝ) / 2 ^ j ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨by positivity, ?_, ?_⟩
  · rw [← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hq' j)
  · apply one_div_le_one_div_of_le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
end Formalism.FourierDecayAlt.P.Sz2
