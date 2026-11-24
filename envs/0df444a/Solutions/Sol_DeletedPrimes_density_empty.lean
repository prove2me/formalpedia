-- Prove2me | solution 1 for DeletedPrimes.density_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:11:15.008814+00:00
-- url     : https://prove2.me/submissions/72f3019d-2813-43e7-9bad-a88cbebdac01

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_muS_empty_ne_one

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution : density ∅ = 1 := by
  unfold density
  rw [tsum_eq_single 1]
  · simp [muS]
  · intro d hd
    rw [muS_empty_ne_one hd]; simp
end DeletedPrimes
