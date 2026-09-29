-- Prove2me | solution 1 for Freiman.background_short_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:29:53.758191+00:00
-- url     : https://prove2.me/submissions/525048a4-97aa-43ea-9997-41364f2d20fd

import Theorems.Thm_Freiman_background_drop_two_constraints
import Theorems.Thm_Freiman_background_reference_greatest
import Theorems.Thm_Freiman_background_T_value
import Theorems.Thm_Freiman_background_prefix12_comparison
import Theorems.Thm_Freiman_background_prefix12_monotone
import Theorems.Thm_Freiman_background_prefix12_radical
import Theorems.Thm_Freiman_cf_convergence

open Freiman

theorem solution (b : ℕ → ℕ+)
    (hb : ∀ n : ℕ, (b n : ℕ) ≤ 4)
    (h14 : OneSidedAvoidsBlock b [1,4]) (ha : BackgroundAllowed .three b)
    (h0 : (b 0 : ℕ) = 1) (h1 : (b 1 : ℕ) ≤ 2) :
    cfValue b ≤ (2 * Real.sqrt 462 - 29) / 19 := by
  obtain ⟨hbound, hpairs, hallowed⟩ :=
    background_drop_two_constraints b hb h14 ha h0 h1
  have htail : cfValue (fun n => b (n + 2)) ≤ cfValue backgroundT := by
    simpa only [backgroundReference, backgroundReferenceState, Bool.false_eq_true, if_false] using
      background_reference_greatest false (fun n => b (n + 2)) hbound hpairs hallowed
  have hpos : 0 ≤ cfValue (fun n => b (n + 2)) :=
    (cf_convergence (fun n => b (n + 2))).2.2.1.le
  calc
    cfValue b ≤ prefixEval [1,2] (cfValue (fun n => b (n + 2))) :=
      background_prefix12_comparison b h0 h1
    _ ≤ prefixEval [1,2] (cfValue backgroundT) :=
      background_prefix12_monotone _ _ hpos htail
    _ = (2 * Real.sqrt 462 - 29) / 19 := by
      rw [background_T_value, background_prefix12_radical]

