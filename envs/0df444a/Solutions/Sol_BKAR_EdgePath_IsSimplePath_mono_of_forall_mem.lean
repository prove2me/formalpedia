-- Prove2me | solution 1 for BKAR.EdgePath.IsSimplePath.mono_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:52.992078+00:00
-- url     : https://prove2.me/submissions/7df0a847-286d-4e1e-96fc-142e60265fc9

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_EdgePath_IsPath_mono_of_forall_mem

set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsSimplePath
namespace BKAR.EdgePath.IsSimplePath
theorem _root_.solution {S T : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j)
    (hmem : ∀ e ∈ γ, e ∈ T) :
    IsSimplePath T γ i j :=
  ⟨h.1.mono_of_forall_mem hmem, h.2⟩
end BKAR.EdgePath.IsSimplePath
