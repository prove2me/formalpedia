-- Prove2me | solution 1 for DeletedPrimes.floor_theta2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:18:51.973525+00:00
-- url     : https://prove2.me/submissions/af855ed2-19b0-4d49-a053-1c776eb890d9

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_composite_floor
import Theorems.Thm_DeletedPrimes_floor_of_forall_k


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) : dim S / 2 * min (1 / 2) (1 - dim S) ≤ theta2 S :=
  floor_of_forall_k hα1 fun _ hk => composite_floor hα0 hα1 F Q hk
end DeletedPrimes
