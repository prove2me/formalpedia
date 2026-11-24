-- Prove2me | solution 1 for Erdos1219.le_two_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:23.824803+00:00
-- url     : https://prove2.me/submissions/1ccbcd7d-0cdb-4ff1-ab1f-3ca103e8aba7

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {μ : Cardinal.{u}} : μ ≤ 2 ^ μ := (cantor μ).le
end Erdos1219
