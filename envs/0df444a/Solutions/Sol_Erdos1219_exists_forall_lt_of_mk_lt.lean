-- Prove2me | solution 1 for Erdos1219.exists_forall_lt_of_mk_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:41:44.024794+00:00
-- url     : https://prove2.me/submissions/5e957cca-0ccf-4ae5-9bec-f83ea2b5ee02

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]
namespace Erdos1219
theorem _root_.solution (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X)
    {s : Set X} (hs : #s < #X) : ∃ x, ∀ y ∈ s, y < x := by
  rw [← not_isCofinal_iff]
  intro hcof
  have h1 : Order.cof X = #X := by
    rw [← Ordinal.cof_type, ← hX, hreg.cof_ord]
  have h2 := Order.cof_le hcof
  rw [h1] at h2
  exact h2.not_gt hs
end Erdos1219
