-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_small_jump_epsilon_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:50:07.804806+00:00
-- url     : https://prove2.me/submissions/22154742-4124-4203-b008-86a6b48b3042

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_original_abs_jump_finite_tail_lt
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_drop_zero_original_jump_marks
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_nonzero_finite_marks_positive_cutoff
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_public_small_mark_tsum_le_complement
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_jump_subtype_tail_eq_indicator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped BigOperators

/-- Absolutely summable original BV negative jumps have arbitrarily small
total magnitude below a positive source-mark cutoff. -/
theorem solution
    {ι : Type*} [DecidableEq ι] (j : ι → ℝ)
    (hj : Summable (fun i => |j i|))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (∑' i : ι, if |j i| < δ then |j i| else 0) < ε := by
  classical
  obtain ⟨S, hS⟩ :=
    avram_p3_main_public_original_abs_jump_finite_tail_lt j hj ε hε
  obtain ⟨T, hT, hTS⟩ :=
    avram_p3_main_public_drop_zero_original_jump_marks j S
  obtain ⟨δ, hδ, hcut⟩ :=
    avram_p3_main_public_nonzero_finite_marks_positive_cutoff T j hT
  refine ⟨δ, hδ, ?_⟩
  have htail : (∑' i : ι, if i ∈ S then 0 else |j i|) < ε := by
    rw [← avram_p3_main_original_jump_subtype_tail_eq_indicator j S hj]
    exact hS
  calc
    (∑' i : ι, if |j i| < δ then |j i| else 0) ≤
        (∑' i : ι, if i ∈ T then 0 else |j i|) :=
      avram_p3_main_public_small_mark_tsum_le_complement j T δ hj hcut
    _ = (∑' i : ι, if i ∈ S then 0 else |j i|) := hTS
    _ < ε := htail
