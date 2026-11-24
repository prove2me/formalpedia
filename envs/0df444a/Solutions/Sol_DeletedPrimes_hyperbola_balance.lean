-- Prove2me | solution 1 for DeletedPrimes.hyperbola_balance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:29.682586+00:00
-- url     : https://prove2.me/submissions/88304581-ab72-4a03-bc6f-522a5f83ce6b

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {β γ x : ℝ} (hx : 0 < x) (hγβ : γ < β) :
    x ^ β * (x ^ (β / (1 + β - γ))) ^ (γ - β) = x ^ (β / (1 + β - γ)) := by
  have hne : 1 + β - γ ≠ 0 := by linarith
  rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  congr 1
  field_simp
  ring
end DeletedPrimes
