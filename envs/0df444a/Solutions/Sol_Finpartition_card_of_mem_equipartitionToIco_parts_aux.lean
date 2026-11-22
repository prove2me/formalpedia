-- Prove2me | solution 1 for Finpartition.card_of_mem_equipartitionToIco_parts_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:34:52.487031+00:00
-- url     : https://prove2.me/submissions/db007976-25d8-4477-bcff-28f02f495bea

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc

set_option autoImplicit true
open Finset
open Finpartition
namespace Finpartition
theorem _root_.solution {n k i : ℕ} :
    equiEndpoint n k (i + 1) - equiEndpoint n k i = if i < n % k then n / k + 1 else n / k := by
  grind [equiEndpoint]
end Finpartition
