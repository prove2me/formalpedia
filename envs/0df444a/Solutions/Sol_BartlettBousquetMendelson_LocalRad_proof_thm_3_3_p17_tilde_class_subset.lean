-- Prove2me | solution 1 for BartlettBousquetMendelson.LocalRad.proof_thm_3_3_p17_tilde_class_subset
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:53:24.565089+00:00
-- url     : https://prove2.me/submissions/0ac36910-2d3f-40d6-827e-31ae755aedf6

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_starHull
import Definitions.Def_BartlettBousquetMendelson_LocalRad_tildeClass

open BartlettBousquetMendelson.LocalRad in
theorem solution {X : Type*} (F : Set (X → ℝ))
    (T : (X → ℝ) → ℝ) (r : ℝ) (hr : 0 < r)
    (hTscale : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (α • f) ≤ α ^ 2 * T f) :
    tildeClass F T r ⊆ {g | g ∈ starHull F 0 ∧ T g ≤ r} := by
  rintro g ⟨f, hf, rfl⟩
  have hmax : r ≤ max (T f) r := le_max_right _ _
  have hmpos : 0 < max (T f) r := lt_of_lt_of_le hr hmax
  have hα : r / max (T f) r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.le hmpos.le, (div_le_one hmpos).mpr hmax⟩
  refine ⟨⟨f, hf, _, hα, by simp⟩, ?_⟩
  refine le_trans (hTscale f hf _ hα) ?_
  rcases le_or_gt (T f) r with h | h
  · rw [max_eq_right h, div_self hr.ne']; simpa using h
  · rw [max_eq_left h.le]
    have hTpos : 0 < T f := lt_trans hr h
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_pos hr hTpos).le (sub_nonneg.mpr h.le)]
