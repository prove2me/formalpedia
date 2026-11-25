-- Prove2me | solution 1 for ErdosPosa.IsMax023.exists_W
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:34:36.520941+00:00
-- url     : https://prove2.me/submissions/32696283-5e6f-4cc9-a44b-f94906679011

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
public import Theorems.Thm_ErdosPosa_IsMax023_no_cyc_R
public import Theorems.Thm_ErdosPosa_cyc_mono


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}
namespace ErdosPosa
namespace IsMax023
theorem _root_.solution (hH : IsMax023 G H) {T : Set V} (hTc : Cyc G T)
    (hT3 : ∀ v ∈ T, deg H v ≠ 3) : ∃ w ∈ T, deg H w = 2 := by
  by_contra hcon
  push Not at hcon
  refine hH.no_cyc_R (cyc_mono hTc le_rfl ?_)
  intro v hv
  rcases hH.2.1 v with h | h | h
  · exact h
  · exact absurd h (hcon v hv)
  · exact absurd h (hT3 v hv)
end IsMax023
end ErdosPosa
