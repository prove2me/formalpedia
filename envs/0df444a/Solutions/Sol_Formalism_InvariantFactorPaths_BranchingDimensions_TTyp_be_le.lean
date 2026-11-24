-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.217399+00:00
-- url     : https://prove2.me/submissions/9c96f1d2-8227-490f-8e2d-0039362c3149

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf

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
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (D : Letters) {a : ℝ} (ha : 0 ≤ a) (h : ∀ i, 1 ≤ i → i ≤ D.n0 → (D.B i : ℝ) ≤ 2 * a) :
    (D.be : ℝ) ≤ 2 * a * D.Ns := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.be
  push_cast
  have hn : (D.n0 : ℝ) ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.n0
    exact_mod_cast Nat.sub_le _ _
  calc (∑ i ∈ Icc 1 D.n0, (D.B i : ℝ)) ≤ ∑ i ∈ Icc 1 D.n0, 2 * a :=
        Finset.sum_le_sum (fun i hi => by
          rw [Finset.mem_Icc] at hi
          exact h i hi.1 hi.2)
    _ = (D.n0 : ℝ) * (2 * a) := by simp
    _ ≤ 2 * a * D.Ns := by nlinarith
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
