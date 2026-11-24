-- Prove2me | solution 1 for DeletedPrimes.dim_eq_zero_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:40.935095+00:00
-- url     : https://prove2.me/submissions/5684fe83-24b3-4aea-b0de-2062eb6faf27

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_dim_eq_zero_of_theta2
import Theorems.Thm_DeletedPrimes_theta2_le_theta
import Theorems.Thm_DeletedPrimes_theta2_nonneg


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (F : Frame S) (Q : Quantization S)
    (L : LandauAtOne S) (h : theta S = 0) : dim S = 0 := by
  have h2 : theta2 S = 0 := le_antisymm (h ▸ theta2_le_theta S) (theta2_nonneg S)
  exact dim_eq_zero_of_theta2 F Q L h2
end DeletedPrimes
