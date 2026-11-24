-- Prove2me | solution 1 for ChromaticReconstruction.leafExt_adj_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:29.324804+00:00
-- url     : https://prove2.me/submissions/0c4fcdcd-be88-46a3-8184-566a8ac145bd

import Definitions.Def_RequestProject_PhiFormula
import Definitions.Def_RequestProject_LeafExtMaster

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K] (S : SimpleGraph K) (m : K → ℕ)
variable {S m}
omit [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution {i : K} {l : Σ i, Fin (m i)} :
    (leafExt S m).Adj (.inl i) (.inr l) ↔ l.1 = i := Iff.rfl
end ChromaticReconstruction
