-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_turn13_original_magnitude_ofReal_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:21:27.21224+00:00
-- url     : https://prove2.me/submissions/11b8a3db-e3ea-4e05-af60-b2197c49dcbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Negative original strict jumps give nonnegative real magnitudes, so the
finite sum commutes with `ENNReal.ofReal`. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let S : Ω → Finset ℝ≥0 := fun ω =>
      (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    let M : Ω → ℝ := fun ω => ∑ u ∈ S ω,
      -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
    ∀ ω : Ω, 0 ≤ M ω ∧
      (∑ u ∈ S ω, ENNReal.ofReal
        (-(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
      ENNReal.ofReal (M ω) := by
  let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
  let S : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
  let M : Ω → ℝ := fun ω => ∑ u ∈ S ω,
    -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  change ∀ ω : Ω, 0 ≤ M ω ∧
    (∑ u ∈ S ω, ENNReal.ofReal
      (-(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) =
    ENNReal.ofReal (M ω)
  intro ω
  let f : ℝ≥0 → ℝ := fun u =>
    -(X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  have hf (u : ℝ≥0) (hu : u ∈ S ω) : 0 ≤ f u := by
    have hmem : u ∈ {v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v <
        -(1 / ((k : ℝ) + 1))} := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hu
    have hcut : -(1 / ((k : ℝ) + 1)) ≤ 0 :=
      neg_nonpos.mpr (by positivity)
    have hjump :
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤ 0 :=
      le_of_lt (lt_of_lt_of_le hmem.2.2 hcut)
    exact neg_nonneg.mpr hjump
  have hfin (s : Finset ℝ≥0) (hs : s ⊆ S ω) :
      0 ≤ ∑ u ∈ s, f u ∧
        (∑ u ∈ s, ENNReal.ofReal (f u)) =
          ENNReal.ofReal (∑ u ∈ s, f u) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert u s hus ih =>
      have hu : u ∈ S ω := hs (Finset.mem_insert_self _ _)
      have hs' : s ⊆ S ω := by
        intro v hv
        exact hs (Finset.mem_insert_of_mem hv)
      obtain ⟨hnon, heq⟩ := ih hs'
      have hupos := hf u hu
      simp only [Finset.sum_insert hus]
      constructor
      · exact add_nonneg hupos hnon
      · rw [heq, ENNReal.ofReal_add hupos hnon]
  simpa only [M, f] using hfin (S ω) (Subset.rfl)
