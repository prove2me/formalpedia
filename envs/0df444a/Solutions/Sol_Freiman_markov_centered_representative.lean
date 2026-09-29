-- Prove2me | solution 1 for Freiman.markov_centered_representative
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:06.159077+00:00
-- url     : https://prove2.me/submissions/0a8af8a2-6185-4299-8632-5c7d09cad982

import Theorems.Thm_Freiman_supremum_approximating_sequence
import Theorems.Thm_Freiman_digits_bounded_of_local_bound
import Theorems.Thm_Freiman_bounded_words_subsequence
import Theorems.Thm_Freiman_localValue_coordinate_limit
import Theorems.Thm_Freiman_localValue_shift

open Freiman Filter

theorem solution (a : ℤ → ℕ+) (t : ℝ)
    (hmax : ∀ i : ℤ, localValue a i ≤ t)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ i : ℤ, t - ε < localValue a i) :
    ∃ b : ℤ → ℕ+, localValue b 0 = t ∧
      ∀ i : ℤ, localValue b i ≤ t := by
  obtain ⟨M, hbound⟩ := digits_bounded_of_local_bound a t hmax
  obtain ⟨u, hlim⟩ := supremum_approximating_sequence (localValue a) t hmax happrox
  have hwords : ∀ i : ℤ, ∀ᶠ n in atTop, (a (u n + i) : ℕ) ≤ M :=
    fun i => Eventually.of_forall (fun n => hbound (u n + i))
  obtain ⟨v, hv, b, _, hagree⟩ := bounded_words_subsequence (fun n i => a (u n + i)) M hwords
  have hcont := localValue_coordinate_limit (fun n i => a (u (v n) + i)) b hagree
  refine ⟨b, ?_, ?_⟩
  · have hzero : Tendsto (fun n => localValue a (u (v n))) atTop
        (nhds (localValue b 0)) := by
      simpa only [localValue_shift, Int.add_zero] using hcont 0
    exact tendsto_nhds_unique hzero (hlim.comp hv.tendsto_atTop)
  · intro i
    apply le_of_tendsto (hcont i)
    filter_upwards [] with n
    rw [localValue_shift]
    exact hmax _

