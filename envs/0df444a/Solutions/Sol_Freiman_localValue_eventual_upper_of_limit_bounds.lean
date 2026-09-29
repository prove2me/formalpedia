-- Prove2me | solution 1 for Freiman.localValue_eventual_upper_of_limit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:06.295845+00:00
-- url     : https://prove2.me/submissions/3c4b6074-0fd2-47c0-91d6-37a69822e1dc

import Theorems.Thm_Freiman_exceedance_subsequence
import Theorems.Thm_Freiman_bounded_words_subsequence
import Theorems.Thm_Freiman_localValue_coordinate_limit
import Theorems.Thm_Freiman_localValue_shift
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith

open Freiman Filter

theorem solution (b : ℤ → ℕ+) (t : ℝ)
    (hfinite : ∃ M : ℕ, ∀ i : ℤ, (b i : ℕ) ≤ M)
    (hlimits : ∀ (u : ℕ → ℕ), StrictMono u → ∀ y : ℤ → ℕ+,
      (∀ i : ℤ, ∀ᶠ n in Filter.atTop, b ((u n : ℤ) + i) = y i) →
      localValue y 0 ≤ t) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ,
      N ≤ n → localValue b (n : ℤ) ≤ t + ε := by
  classical
  by_contra hupper
  push Not at hupper
  obtain ⟨ε, hε, hbad⟩ := hupper
  obtain ⟨M, hbound⟩ := hfinite
  obtain ⟨u, hu, hexceed⟩ := exceedance_subsequence
    (fun n : ℕ => localValue b (n : ℤ)) (t + ε) hbad
  have hwords : ∀ i : ℤ, ∀ᶠ n in atTop, (b ((u n : ℤ) + i) : ℕ) ≤ M :=
    fun i => Eventually.of_forall (fun n => hbound ((u n : ℤ) + i))
  obtain ⟨v, hv, y, _, hagree⟩ := bounded_words_subsequence
    (fun n i => b ((u n : ℤ) + i)) M hwords
  have hle := hlimits (fun n => u (v n)) (hu.comp hv) y hagree
  have hcont := localValue_coordinate_limit
    (fun n i => b ((u (v n) : ℤ) + i)) y hagree
  have hge : t + ε ≤ localValue y 0 := by
    apply ge_of_tendsto (hcont 0)
    filter_upwards [] with n
    simpa only [localValue_shift, Int.add_zero] using (hexceed (v n)).le
  linarith
