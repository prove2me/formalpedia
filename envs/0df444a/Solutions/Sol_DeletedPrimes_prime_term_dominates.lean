-- Prove2me | solution 1 for DeletedPrimes.prime_term_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:21:03.227221+00:00
-- url     : https://prove2.me/submissions/8a0ef6d6-c9a1-475b-a5aa-a4850ddb5023

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α β x : ℝ} (hβ : β < 1 / 2) (hα : 1 / 2 < α) (hx : 1 ≤ x) :
    x ^ β ≤ x ^ α ∧ x ^ (1 / 2 : ℝ) ≤ x ^ α :=
  ⟨Real.rpow_le_rpow_of_exponent_le hx (by linarith), Real.rpow_le_rpow_of_exponent_le hx hα.le⟩
end DeletedPrimes
