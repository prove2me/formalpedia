-- Prove2me | solution 1 for Csg.NCSG.combine_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:06.186282+00:00
-- url     : https://prove2.me/submissions/041cfabb-f90f-4c9e-ad66-7776d6f28aca

import Definitions.Def_Csg_Coalition
import Definitions.Def_Csg_CoalitionComplement

set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
omit [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
namespace Csg.NCSG
theorem _root_.solution (y : ComplementAction A C) (x : ComplementAction A Cᶜ) :
    combine Cᶜ y x = combine C (complCoalitionEquiv C x) y := by
  funext i
  by_cases h : i ∈ C
  · have h' : i ∉ Cᶜ := by simp [h]
    simp [combine, complCoalitionEquiv, dif_pos h]
  · have h' : i ∈ Cᶜ := by simp [h]
    simp [combine, dif_neg h]
end Csg.NCSG
