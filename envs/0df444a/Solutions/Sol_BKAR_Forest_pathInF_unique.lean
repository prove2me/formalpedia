-- Prove2me | solution 1 for BKAR.Forest.pathInF_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:52.364442+00:00
-- url     : https://prove2.me/submissions/db3e7400-bbad-456b-b433-38afe4e7192c

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_Forest_pathInF_isSimple

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {i j : V}
    (h : F.inSameComponent i j) (γ : List (Edge V))
    (hγ : IsSimplePath F γ i j) :
    γ = F.pathInF i j h :=
  F.acyclic.path_unique hγ (F.pathInF_isSimple h)
end BKAR.Forest
