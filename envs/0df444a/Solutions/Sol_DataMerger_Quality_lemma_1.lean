-- Prove2me | solution 1 for DataMerger.Quality.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:23:38.795984+00:00
-- url     : https://prove2.me/submissions/69f1dad9-0dcf-4a8b-8f66-f45a901276d6

import Mathlib
import Definitions.Def_DataMerger_Quality_Model

open DataMerger.Quality in
theorem solution (pi : ℝ → ℝ → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    allocI pi δ = allocM pi δ ∧
      (ExclusiveI pi δ ↔ ExclusiveM pi δ) ∧
      (ExclusiveI pi δ ↔ 2 * pi δ δ < pi δ 0 + pi 0 δ) := by
  have h1 : ExclusiveI pi δ ↔ 2 * pi δ δ < pi δ 0 + pi 0 δ := by
    unfold ExclusiveI T1 T2; constructor <;> intro h <;> linarith
  have h2 : ExclusiveM pi δ ↔ 2 * pi δ δ < pi δ 0 + pi 0 δ := by
    unfold ExclusiveM T2; constructor <;> intro h <;> linarith
  have h3 : ExclusiveI pi δ ↔ ExclusiveM pi δ := h1.trans h2.symm
  refine ⟨?_, h3, h1⟩
  unfold allocI allocM
  by_cases h : ExclusiveI pi δ
  · rw [if_pos h, if_pos (h3.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (h3.mpr h'))]
