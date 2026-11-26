-- Prove2me | solution 1 for BKAR.Forest.EdgeExtension.mem_old_of_mem_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:04:08.693472+00:00
-- url     : https://prove2.me/submissions/5ae4da3b-e2e2-48de-8964-f170b876c080

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
theorem _root_.solution (h : EdgeExtension F F' e₀)
    (he : e ∈ F'.edges) (hne : e ≠ e₀) : e ∈ F.edges := by
  have hmem : e ∈ insert e₀ F.edges := by
    rw [← h.edges_eq]
    exact he
  rw [Finset.mem_insert] at hmem
  exact hmem.elim (fun heq => False.elim (hne heq)) id
end BKAR.Forest.EdgeExtension
