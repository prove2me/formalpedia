-- Prove2me | solution 1 for Freiman.attain_limsup_by_shift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:21:52.628282+00:00
-- url     : https://prove2.me/submissions/8b33682c-1fab-43c9-a873-5c09cdd146d3

import Theorems.Thm_Freiman_eventual_digits_bounded
import Theorems.Thm_Freiman_limsup_subsequence
import Theorems.Thm_Freiman_shifted_words_subsequence
import Theorems.Thm_Freiman_localValue_coordinate_limit
import Theorems.Thm_Freiman_localValue_shift
import Theorems.Thm_Freiman_localValue_shift_limit_le

open Freiman Filter

theorem solution (a : ℤ → ℕ+) (t : ℝ)
    (h : HasFiniteLimsup (fun n : ℕ => localValue a (n : ℤ)) t) :
    ∃ b : ℤ → ℕ+, localValue b 0 = t ∧
      ∀ i : ℤ, localValue b i ≤ t := by
  obtain ⟨M, N, hbound⟩ := eventual_digits_bounded a t h
  obtain ⟨u, hu, hlim⟩ := limsup_subsequence (fun n : ℕ => localValue a (n : ℤ)) t h
  obtain ⟨v, hv, b, _, hagree⟩ := shifted_words_subsequence a M N hbound u hu
  have hcont := localValue_coordinate_limit
    (fun n j => a ((u (v n) : ℤ) + j)) b hagree
  refine ⟨b, ?_, ?_⟩
  · have hzero : Tendsto (fun n => localValue a (u (v n) : ℤ)) atTop
        (nhds (localValue b 0)) := by
      simpa only [localValue_shift, Int.add_zero] using hcont 0
    exact tendsto_nhds_unique hzero (hlim.comp hv.tendsto_atTop)
  · intro i
    apply localValue_shift_limit_le a t h (fun n => u (v n)) (hu.comp hv) i
      (localValue b i)
    simpa only [localValue_shift] using hcont i

