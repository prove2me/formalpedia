-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.WGT.antitone_of_mem_stripsUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:00.803451+00:00
-- url     : https://prove2.me/submissions/38819954-fbfe-4937-be87-0e6d8f90ac4e

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementW
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_WeylGT
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_extW_lt
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_WGT_dom_iff

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
theorem _root_.solution {n : ℕ} {μ ν : Fin n → ℤ} {B : ℕ} (h : ν ∈ stripsUp μ B) : Antitone ν := by
  classical
  unfold stripsUp at h
  simp only [Finset.mem_filter] at h
  obtain ⟨_, hle, hadj, _⟩ := h
  apply (dom_iff ν).mp
  intro m hm
  rw [extW_lt ν hm, extW_lt ν (by omega)]
  exact le_trans (hadj ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl) (hle _)
end Formalism.InvariantFactorPaths.BranchingDimensions.WGT
