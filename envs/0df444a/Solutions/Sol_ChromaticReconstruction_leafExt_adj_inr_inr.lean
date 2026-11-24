-- Prove2me | solution 1 for ChromaticReconstruction.leafExt_adj_inr_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:20.273883+00:00
-- url     : https://prove2.me/submissions/51f02c3d-4594-47e1-8a06-d40034980b78

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
theorem _root_.solution {l l' : Σ i, Fin (m i)} :
    ¬ (leafExt S m).Adj (.inr l) (.inr l') := id
end ChromaticReconstruction
