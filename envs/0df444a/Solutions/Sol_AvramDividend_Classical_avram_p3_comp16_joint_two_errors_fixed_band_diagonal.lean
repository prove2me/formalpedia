-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp16_joint_two_errors_fixed_band_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:06:04.518134+00:00
-- url     : https://prove2.me/submissions/00bf6b75-914d-4598-9063-fbfb095ae678

import Mathlib.Analysis.Normed.Group.Continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp16_diagonal_from_pointwise_fixed_band_errors

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
noncomputable section

/-! A single diagonal schedule simultaneously controls both localised errors. -/
theorem solution
    (ErrCell ErrContact : ℕ → ℕ → ℝ)
    (hCell : ∀ k, Tendsto (fun n => ErrCell k n) atTop (nhds 0))
    (hContact : ∀ k, Tendsto (fun n => ErrContact k n) atTop (nhds 0)) :
    ∃ κ : ℕ → ℕ,
      (∀ n, κ n ≤ n) ∧
      Tendsto κ atTop atTop ∧
      Tendsto (fun n => ErrCell (κ n) n) atTop (nhds 0) ∧
      Tendsto (fun n => ErrContact (κ n) n) atTop (nhds 0) := by
  have hFix : ∀ k : ℕ,
      Tendsto (fun n => |ErrCell k n| + |ErrContact k n|)
        atTop (nhds (0 : ℝ)) := by
    intro k
    simpa using ((hCell k).abs.add (hContact k).abs)
  obtain ⟨κ, hκle, hκtop, hsum⟩ :=
    AvramDividend.Classical.avram_p3_comp16_diagonal_from_pointwise_fixed_band_errors
      (fun k n => |ErrCell k n| + |ErrContact k n|) hFix
  have hfirst :
      Tendsto (fun n => ErrCell (κ n) n) atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero_norm'
      (a := fun n => |ErrCell (κ n) n| + |ErrContact (κ n) n|)
    · exact Filter.Eventually.of_forall (fun n => by
        rw [Real.norm_eq_abs]
        exact le_add_of_nonneg_right (abs_nonneg _))
    · exact hsum
  have hsecond :
      Tendsto (fun n => ErrContact (κ n) n) atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero_norm'
      (a := fun n => |ErrCell (κ n) n| + |ErrContact (κ n) n|)
    · exact Filter.Eventually.of_forall (fun n => by
        rw [Real.norm_eq_abs]
        exact le_add_of_nonneg_left (abs_nonneg _))
    · exact hsum
  exact ⟨κ, hκle, hκtop, hfirst, hsecond⟩
