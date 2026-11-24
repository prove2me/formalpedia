-- Prove2me | solution 1 for DeletedPrimes.boundary_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:15:42.269617+00:00
-- url     : https://prove2.me/submissions/e14f30c3-ca09-4aee-a61f-4d4812bb3f05

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α κ : ℝ} (h1 : α < 1) (hκ : κ < 1 / 2) : (1 - α) * (2 * κ - 1) < 0 :=
  mul_neg_of_pos_of_neg (by linarith) (by linarith)
end DeletedPrimes
