-- Prove2me | solution 1 for Erdos1219.two_pow_pow_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:21.203894+00:00
-- url     : https://prove2.me/submissions/2d7a244c-9ad3-41d2-b45d-1de082325fd3

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    ((2 : Cardinal.{u}) ^ μ) ^ μ = 2 ^ μ := by
  rw [← power_mul, mul_eq_self hμ]
end Erdos1219
