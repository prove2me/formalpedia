-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.a_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.086421+00:00
-- url     : https://prove2.me/submissions/9ff27c3b-b2f1-4b8b-a1c5-d2bb1afcd7fb

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace TTyp
end TTyp
private theorem le_div_of_mul_le_of_pos' {x y z : ℝ} (hz : 0 < z) (h : x * z ≤ y) : x ≤ y / z := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have e : y / z * z = y := by field_simp
  nlinarith
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
end TTyp
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution {La b p k k' g : ℝ} (hLa : 0 < La) (hp : 0 < p) (hk : 0 < k) (hk' : 0 ≤ k')
    (hg0 : 0 < g) (hg : g ≤ 4 * b / p) : La * k' / (16 * k) ≤ (La * b / (p * k)) * k' / (4 * g) := by
  have hpos : 0 ≤ La * k' / (4 * k) := div_nonneg (mul_nonneg hLa.le hk') (by linarith)
  refine _root_.Formalism.InvariantFactorPaths.BranchingDimensions.le_div_of_mul_le_of_pos' (by linarith) ?_
  calc La * k' / (16 * k) * (4 * g) = La * k' / (4 * k) * g := by ring
    _ ≤ La * k' / (4 * k) * (4 * b / p) := mul_le_mul_of_nonneg_left hg hpos
    _ = La * b / (p * k) * k' := by ring
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
