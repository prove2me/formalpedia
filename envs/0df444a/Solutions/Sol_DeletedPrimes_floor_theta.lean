-- Prove2me | solution 1 for DeletedPrimes.floor_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:15.658801+00:00
-- url     : https://prove2.me/submissions/09678f6f-793b-43f3-b4f0-3e08f241549d

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_floor_theta2
import Theorems.Thm_DeletedPrimes_theta2_le_theta


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) : dim S / 2 * min (1 / 2) (1 - dim S) ≤ theta S :=
  (floor_theta2 hα0 hα1 F Q).trans (theta2_le_theta S)
end DeletedPrimes
