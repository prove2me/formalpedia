-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.rpow_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:11.538683+00:00
-- url     : https://prove2.me/submissions/6a898df4-c4cf-4eb5-b86b-d0fb5be7af7d

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution {N : ℝ} (hN : 2 ≤ N) {M : ℕ} (hM : 3 ≤ M) :
    N ^ (-(M : ℝ) / 2) ≤ 1 / N ^ ((3 : ℝ) / 2) ∧ 1 / N ^ ((3 : ℝ) / 2) ≤ 1 / 2 := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  constructor
  · rw [one_div, ← Real.rpow_neg hN0.le]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have : (3 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  · have h2 : (2 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := by
      calc (2 : ℝ) ≤ N := hN
        _ = N ^ (1 : ℝ) := (Real.rpow_one N).symm
        _ ≤ N ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
end Formalism.MainNotions.MassRatioZetaBound
