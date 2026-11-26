-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.old_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:05.659599+00:00
-- url     : https://prove2.me/submissions/42592594-9233-4add-8f36-aef5e377b989

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ e : Edge V}
namespace BKAR.Forest.EdgeExtension
theorem _root_.solution (h : EdgeExtension F F' e₀) (he : e ∈ F.edges) :
    e ∈ F'.edges := by
  rw [h.edges_eq]
  exact Finset.mem_insert_of_mem he
end BKAR.Forest.EdgeExtension
