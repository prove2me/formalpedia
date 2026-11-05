-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_source_tagged_capture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:54:26.851415+00:00
-- url     : https://prove2.me/submissions/204036ec-7637-442c-850c-b2b4e9f3cbde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ) (T : Finset ℝ≥0)
    (hCover : ∀ v ∈ T, ∃ i : ℕ,
      i < n ∧ u i < v ∧ v ≤ u (i + 1))
    (hSeparate : ∀ v ∈ T, ∀ z ∈ T, ∀ i : ℕ,
      i < n → u i < v → v ≤ u (i + 1) →
      u i < z → z ≤ u (i + 1) → v = z) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      ∃ tag : ℝ≥0 → ℕ,
        (∀ v ∈ T,
          tag v < n ∧ u (tag v) < v ∧ v ≤ u (tag v + 1)) ∧
        (∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z) ∧
        T.sum (fun v =>
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) ≤
          (Finset.range n).sum (fun i =>
            if i ∈ T.image tag then
              J (u (i + 1)) - J (u i) else 0) := by
  classical
  filter_upwards
    [avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell X hBV]
      with ω hω
  intro J
  let tag : ℝ≥0 → ℕ := fun v =>
    if hv : v ∈ T then Classical.choose (hCover v hv) else 0
  have hcell : ∀ v ∈ T,
      tag v < n ∧ u (tag v) < v ∧ v ≤ u (tag v + 1) := by
    intro v hv
    have hvCell := Classical.choose_spec (hCover v hv)
    simpa only [tag, dif_pos hv] using hvCell
  have hinj : ∀ v ∈ T, ∀ z ∈ T,
      tag v = tag z → v = z := by
    intro v hv z hz heq
    have hvCell := hcell v hv
    have hzCell := hcell z hz
    have hzStart : u (tag v) < z := by
      rw [heq]
      exact hzCell.2.1
    have hzEnd : z ≤ u (tag v + 1) := by
      rw [heq]
      exact hzCell.2.2
    exact hSeparate v hv z hz (tag v) hvCell.1
      hvCell.2.1 hvCell.2.2 hzStart hzEnd
  have hAtom : ∀ v ∈ T,
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω ≤
        J (u (tag v + 1)) - J (u (tag v)) := by
    intro v hv
    have hvCell := hcell v hv
    exact hω (u (tag v)) (u (tag v + 1)) v hvCell.2.1 hvCell.2.2
  refine ⟨tag, hcell, hinj, ?_⟩
  exact avram_p3_f_chainlimit_original_finite_atom_cell_capture
    X hBV u n T tag (fun v hv => (hcell v hv).1)
    hinj ω hAtom
