-- Prove2me | solution 1 for Erdos1219.aleph_nat_le_aleph_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:26.502998+00:00
-- url     : https://prove2.me/submissions/bf911688-ef51-4ba6-9fcd-cd710ba920a2

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution (N : ℕ) : ℵ_ (N : Ordinal.{u}) ≤ ℵ_ ω :=
  aleph_le_aleph.2 (natCast_lt_omega0 N).le
end Erdos1219
