-- Prove2me | solution 1 for DeletedPrimes.hyperbola_exponent_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:19:02.984723+00:00
-- url     : https://prove2.me/submissions/99726e4f-ed7d-4e35-ba61-fcd86c4d68e3

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β) : β / (1 + β - γ) < β := by
  have hpos : 0 < 1 + β - γ := by linarith
  rw [div_lt_iff₀ hpos]
  nlinarith
end DeletedPrimes
