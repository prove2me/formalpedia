-- Prove2me | solution 1 for Freiman.perron_formula
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:24:17.663967+00:00
-- url     : https://prove2.me/submissions/ce78fffa-cc97-46c9-ba78-db8cb1ed71c2

import Definitions.Def_Freiman_cfValue
import Definitions.Def_Freiman_lagrangeSpectrum
import Theorems.Thm_Freiman_finite_limsup_subsequence_comparison
import Theorems.Thm_Freiman_continuant_denominator_escape
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_perron_convergent_subsequence
import Theorems.Thm_Freiman_perron_arbitrary_error_control
import Theorems.Thm_Freiman_perron_frequently_at_least_two

open Freiman

theorem solution (b : ℕ → ℕ+) (t : ℝ) :
    HasFiniteLimsup (fun n : ℕ => approximationValue (cfValue b) (n + 1)) t ↔
    HasFiniteLimsup (perronValue b) t := by
  apply finite_limsup_subsequence_comparison
    (fun n => approximationValue (cfValue b) (n + 1)) (perronValue b)
    (fun n => continuantQ b n - 1) t
  · intro R
    obtain ⟨N, hN⟩ := continuant_denominator_escape b (R + 1)
    exact ⟨N, fun n hn => by have := hN n hn; omega⟩
  · obtain ⟨N, hN⟩ := perron_convergent_subsequence b
    refine ⟨N, ?_⟩
    intro n hn
    have hp : 0 < continuantQ b n := continuant_denominator_pos _
    simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hp))] using hN n hn
  · exact perron_arbitrary_error_control b
  · exact perron_frequently_at_least_two b
