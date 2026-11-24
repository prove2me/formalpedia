-- Prove2me | solution 1 for ChromaticReconstruction.leafExt_adj_inr_inl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:46.841273+00:00
-- url     : https://prove2.me/submissions/c08cbd2f-f9b2-4b6e-b4db-5e2d4820cc25

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
    (leafExt S m).Adj (.inr l) (.inl i) ↔ l.1 = i := Iff.rfl
end ChromaticReconstruction
