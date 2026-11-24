-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_Mpi_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:04.969518+00:00
-- url     : https://prove2.me/submissions/bc258373-c644-4f66-9e13-1816fc5c0523

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_ev_zero_of_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_mem_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) (hpi : DomLowerSet pi) :
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} := by
  apply le_antisymm
  · unfold ColFam.Mpi
    rw [Submodule.span_le]
    rintro x ⟨j, hj, I, rfl⟩
    exact qb_mem_std hA CF pi hpi _ fun mu hmu hout => qb_ev_zero_of_mem CF ℚ hpi hj I hmu hout
  · apply Submodule.span_mono
    rintro x ⟨j, hj, I, -, rfl⟩
    exact ⟨j, hj, I, rfl⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
