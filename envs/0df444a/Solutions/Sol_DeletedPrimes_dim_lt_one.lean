-- Prove2me | solution 1 for DeletedPrimes.dim_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:18.051851+00:00
-- url     : https://prove2.me/submissions/3604f6bc-3d74-4299-8f52-61ea9b75b9ba

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (L : LandauAtOne S) (h : theta2 S < 1) : dim S < 1 := L h
end DeletedPrimes
