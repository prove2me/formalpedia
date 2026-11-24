-- Prove2me | solution 1 for DeletedPrimes.lt_pow_floor_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:38.767801+00:00
-- url     : https://prove2.me/submissions/a7353ff2-98b1-4375-85f2-383213b1272a

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {N Y : ℕ} (hN : 1 ≤ N) (hY : 2 ≤ Y) :
    N < Y ^ (⌊Real.log N / Real.log Y⌋₊ + 1) := by
  set L := ⌊Real.log N / Real.log Y⌋₊
  have hYr : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogY : 0 < Real.log Y := Real.log_pos hYr
  have h1 : Real.log N / Real.log Y < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : Real.log N < ((L : ℝ) + 1) * Real.log Y := (div_lt_iff₀ hlogY).mp h1
  have h3 : Real.log N < Real.log ((Y : ℝ) ^ (L + 1)) := by
    rw [Real.log_pow]; push_cast; exact h2
  have h4 : (N : ℝ) < (Y : ℝ) ^ (L + 1) :=
    (Real.log_lt_log_iff hNr (by positivity)).mp h3
  exact_mod_cast h4
end DeletedPrimes
