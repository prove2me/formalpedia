-- Prove2me | solution 1 for DeletedPrimes.theta2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:10:06.016802+00:00
-- url     : https://prove2.me/submissions/9c905ab1-0920-491f-b041-c7d408ec9746

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta2_set_one_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : 0 ≤ theta2 S :=
  le_csInf ⟨1, theta2_set_one_mem S⟩ fun _ h => h.1
end DeletedPrimes
