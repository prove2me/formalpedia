-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_K4_right_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:55.977881+00:00
-- url     : https://prove2.me/submissions/99d84bfd-7899-4487-a7fa-263a0b4d355f

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_owner_excludes_k3

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    Disjoint (paper11K3RightVertices G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) := by
  rw [Finset.disjoint_left]
  intro u hu3 hu4
  exact paper11K4_owner_excludes_k3 G hCan hmax hu4 hu3
end C6BipartiteDomination
