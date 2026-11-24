-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_Mpi_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:08.659555+00:00
-- url     : https://prove2.me/submissions/af1884f2-15d8-430c-a8a6-6cf0e5cd8ee3

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_Mpi_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_basis_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_vecF_int


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
    CF.Mpi pi = Submodule.span ℤ (qb_basis hA CF ℤ '' {y | CF.mu y.1 ∈ pi}) := by
  rw [qb_Mpi_eq hA CF pi hpi]
  congr 1
  ext x
  constructor
  · rintro ⟨j, hj, I, hI, rfl⟩
    exact ⟨⟨j, I, hI⟩, hj, by rw [qb_basis_apply, qb_vecF_int]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, hy, y.2.1, y.2.2, by rw [qb_basis_apply, qb_vecF_int]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
