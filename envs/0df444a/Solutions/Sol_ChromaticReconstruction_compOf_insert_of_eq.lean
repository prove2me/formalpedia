-- Prove2me | solution 1 for ChromaticReconstruction.compOf_insert_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:39.984529+00:00
-- url     : https://prove2.me/submissions/e6077cc6-588e-4693-afbc-c609028d00fa

import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Forest
import Theorems.Thm_ChromaticReconstruction_compOf_eq_iff
import Theorems.Thm_ChromaticReconstruction_reachable_mono


set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]
namespace ChromaticReconstruction
theorem _root_.solution {A : Set (Sym2 V)} {e : Sym2 V} {x y : V}
    (h : compOf A x = compOf A y) : compOf (insert e A) x = compOf (insert e A) y :=
  compOf_eq_iff.2 (reachable_mono (Set.subset_insert _ _) (compOf_eq_iff.1 h))
end ChromaticReconstruction
