-- Prove2me | solution 1 for DeletedPrimes.theta_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:06:49.300865+00:00
-- url     : https://prove2.me/submissions/8d15792e-747c-4ef9-ad28-76e2c97c1d1f

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta_set_bddBelow
import Theorems.Thm_DeletedPrimes_theta_set_one_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : theta S ≤ 1 :=
  csInf_le (theta_set_bddBelow S) (theta_set_one_mem S)
end DeletedPrimes
