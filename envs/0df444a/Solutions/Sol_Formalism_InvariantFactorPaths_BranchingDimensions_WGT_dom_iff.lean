-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.WGT.dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:36:11.592001+00:00
-- url     : https://prove2.me/submissions/8a51b984-8078-4227-95e7-ae9ac5984a1a

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_extW_lt

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
open Formalism.InvariantFactorPaths.BranchingDimensions.WGT
open Formalism.InvariantFactorPaths.GelfandTsetlinBases (gtBox dGT stripsUp)
namespace Formalism.InvariantFactorPaths.BranchingDimensions.WGT
theorem _root_.solution {n : ℕ} (μ : Fin n → ℤ) : Dom n (extW μ) ↔ Antitone μ := by
  constructor
  · intro h a b hab
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    simp only [Fin.mk_le_mk] at hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ k hak ih =>
      have h1 := h k hb
      rw [extW_lt μ hb, extW_lt μ (by omega)] at h1
      exact le_trans h1 (ih (by omega))
  · intro h m hm
    rw [extW_lt μ hm, extW_lt μ (by omega)]
    exact h (Fin.mk_le_mk.mpr (Nat.le_succ m))
end Formalism.InvariantFactorPaths.BranchingDimensions.WGT
