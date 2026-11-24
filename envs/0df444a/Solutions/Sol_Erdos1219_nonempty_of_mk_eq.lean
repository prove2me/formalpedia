-- Prove2me | solution 1 for Erdos1219.nonempty_of_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:36.173118+00:00
-- url     : https://prove2.me/submissions/01ec01b7-c707-478a-86c8-7845b8a50719

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V : Type u} {s : Set V} {c : Cardinal.{u}} (hs : #s = c)
    (hc : ℵ₀ ≤ c) : s.Nonempty := by
  have : Nonempty s := mk_ne_zero_iff.1 (by rw [hs]; exact (aleph0_pos.trans_le hc).ne')
  exact Set.nonempty_coe_sort.1 this
end Erdos1219
