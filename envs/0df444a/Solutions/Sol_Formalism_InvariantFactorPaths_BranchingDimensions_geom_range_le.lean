-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.geom_range_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:12.900577+00:00
-- url     : https://prove2.me/submissions/b60db72b-54dc-4f32-944e-409908f39e8b

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementN
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AdmissibleSmallRatio

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : (0:ℝ) < (p:ℝ)^(m0+n) := pow_pos hP0 _
    have e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n) := by
      rw [← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n)) := by ring
    linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
