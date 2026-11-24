-- Prove2me | solution 1 for DeletedPrimes.hyperbola_y_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:07.693837+00:00
-- url     : https://prove2.me/submissions/8d2ce6f8-ef82-4336-ac3e-baad562371b8

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_hyperbola_exponent_mem

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {β γ x : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) (hx : 1 ≤ x) :
    1 ≤ x ^ (β / (1 + β - γ)) ∧ x ^ (β / (1 + β - γ)) ≤ x := by
  obtain ⟨h0, h1⟩ := hyperbola_exponent_mem hγ0 hγβ hβ1
  refine ⟨Real.one_le_rpow hx h0.le, ?_⟩
  calc x ^ (β / (1 + β - γ)) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1
    _ = x := Real.rpow_one x
end DeletedPrimes
