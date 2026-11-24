-- Prove2me | solution 1 for Erdos1219.aleph0_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:42:05.414796+00:00
-- url     : https://prove2.me/submissions/f3338100-1231-4a5f-a94f-e8c2d3399de2

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Theorems.Thm_Erdos1219_le_two_pow_self

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : ℵ₀ ≤ 2 ^ μ :=
  hμ.trans le_two_pow_self
end Erdos1219
