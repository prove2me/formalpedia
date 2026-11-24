-- Prove2me | solution 1 for Erdos1219.exists_gt_of_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:15.225799+00:00
-- url     : https://prove2.me/submissions/37e57cda-541b-4698-b240-07e0d888e8b9

import Definitions.Def_Erdos1219_Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_exists_forall_lt_of_mk_lt

set_option autoImplicit false
open Cardinal Ordinal Set
open Erdos1219
universe u
variable {X : Type u} [LinearOrder X] [WellFoundedLT X]
namespace Erdos1219
theorem _root_.solution (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X) (x : X) :
    ∃ y, x < y := by
  obtain ⟨y, hy⟩ := exists_forall_lt_of_mk_lt hreg hX (s := {x})
    (by rw [mk_singleton]; exact one_lt_aleph0.trans_le hreg.aleph0_le)
  exact ⟨y, hy x (mem_singleton x)⟩
end Erdos1219
