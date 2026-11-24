-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.ent_sign
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.201717+00:00
-- url     : https://prove2.me/submissions/418a576f-b6e6-4458-82c4-18bb85665c0a

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
theorem _root_.solution (h20 : PathEntryBounds) {D : Letters} {mu : D.Stages} (hW : D.Wf) (hP : D.IsPATH mu)
    {i m : ℕ} (hi : i ≤ D.Ns) (hm : m < D.k) :
    (m + D.Ns < D.k → 0 ≤ ent mu i m) ∧ (D.Ns ≤ m → ent mu i m ≤ 0) := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.PathEntryBounds at h20
  have H := (h20 D mu hW hP).2 i hi
  have hv : D.nVec i ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.nVec
    calc _ ≤ (Icc 1 i).card := Finset.card_filter_le _ _
      _ = i := by simp
      _ ≤ D.Ns := hi
  have hc : D.nCov i ≤ D.Ns := by
    unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.nCov
    calc _ ≤ (Icc 1 i).card := Finset.card_filter_le _ _
      _ = i := by simp
      _ ≤ D.Ns := hi
  exact ⟨fun h1 => H.2 m (by omega), fun h1 => H.1 m (by omega) hm⟩
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
