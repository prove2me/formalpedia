-- Prove2me | solution 1 for ChromaticReconstruction.leafExt_adj_inl_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:03.958074+00:00
-- url     : https://prove2.me/submissions/fb27762a-555b-40e1-aa1e-a446ea06fa0a

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
theorem _root_.solution {i j : K} :
    (leafExt S m).Adj (.inl i) (.inl j) ↔ S.Adj i j := Iff.rfl
end ChromaticReconstruction
