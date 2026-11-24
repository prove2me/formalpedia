-- Prove2me | solution 1 for DeletedPrimes.theta_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:06:41.838802+00:00
-- url     : https://prove2.me/submissions/92940846-ab2d-49fe-af5e-94a4cc7eeb7a

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta_set_one_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : 0 ≤ theta S :=
  le_csInf ⟨1, theta_set_one_mem S⟩ fun _ h => h.1
end DeletedPrimes
