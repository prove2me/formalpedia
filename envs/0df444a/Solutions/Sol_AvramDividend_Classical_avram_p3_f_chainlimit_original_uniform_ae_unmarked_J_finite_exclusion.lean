-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_uniform_ae_unmarked_J_finite_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:48:00.901035+00:00
-- url     : https://prove2.me/submissions/31e59b2a-919d-48a5-94c1-d3901cd74b26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_finite_atom_cell_capture
import Theorems.Thm_AvramDividend_Classical_avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      ∀ (u : ℕ → ℝ≥0) (n : ℕ)
        (T : Finset ℝ≥0) (tag : ℝ≥0 → ℕ)
        (hTag : ∀ v ∈ T, tag v < n)
        (hInj : ∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z)
        (hInside : ∀ v ∈ T, u (tag v) < v ∧ v ≤ u (tag v + 1)),
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∑ i ∈ Finset.range n, if i ∈ T.image tag then 0 else j i) ≤
        J (u n) - J (u 0) -
          (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) := by
  filter_upwards
    [avram_p3_f_chainlimit_original_positive_atom_le_actual_J_cell X hBV]
    with ω hAtom
  intro u n T tag hTag hInj hInside J j
  have hCell (v : ℝ≥0) (hv : v ∈ T) :
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω ≤
        j (tag v) := by
    have hi := hInside v hv
    have h := hAtom (u (tag v)) (u (tag v + 1)) v hi.1 hi.2
    change Function.leftLim (fun r : ℝ≥0 => X.X r ω) v -
      X.X v ω ≤ j (tag v) at h
    exact h
  have hCapture :
      (∑ v ∈ T, (Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) ≤
        (∑ i ∈ Finset.range n,
          if i ∈ T.image tag then j i else 0) := by
    simpa only [J, j] using
      (avram_p3_f_chainlimit_original_finite_atom_cell_capture
        X hBV u n T tag hTag hInj ω hCell)
  have hPartition :
      (∑ i ∈ Finset.range n, if i ∈ T.image tag then 0 else j i) +
        (∑ i ∈ Finset.range n,
          if i ∈ T.image tag then j i else 0) =
        J (u n) - J (u 0) := by
    simpa only [J, j] using
      (avram_p3_f_chainlimit_original_negative_jump_unmarked_grid_partition
        X hBV u n (T.image tag) ω)
  linarith
