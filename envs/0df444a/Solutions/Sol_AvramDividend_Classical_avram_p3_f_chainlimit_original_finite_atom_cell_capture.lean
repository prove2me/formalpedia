-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f_chainlimit_original_finite_atom_cell_capture
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:39:21.686411+00:00
-- url     : https://prove2.me/submissions/43bc236f-4f94-493a-a239-65620bbdf268

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (T : Finset ℝ≥0) (tag : ℝ≥0 → ℕ)
    (hTag : ∀ v ∈ T, tag v < n)
    (hInj : ∀ v ∈ T, ∀ z ∈ T, tag v = tag z → v = z) :
    ∀ ω,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s - X.X s ω
        else 0
      let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
      (∀ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω) ≤ j (tag v)) →
      (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) ≤
        (∑ i ∈ Finset.range n, if i ∈ T.image tag then j i else 0) := by
  classical
  intro ω J j hAtom
  have hsubset : T.image tag ⊆ Finset.range n := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨v, hv, rfl⟩
    exact Finset.mem_range.mpr (hTag v hv)
  have hsum :
      (∑ v ∈ T, (Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω)) ≤
      (∑ v ∈ T, j (tag v)) := by
    apply Finset.sum_le_sum
    intro v hv
    exact hAtom v hv
  have himage :
      (∑ v ∈ T, j (tag v)) =
      (∑ i ∈ T.image tag, j i) := by
    symm
    exact Finset.sum_image hInj
  have hmask :
      (∑ i ∈ Finset.range n, if i ∈ T.image tag then j i else 0) =
      (∑ i ∈ T.image tag, j i) := by
    calc
      _ = (∑ i ∈ T.image tag, if i ∈ T.image tag then j i else 0) := by
            symm
            apply Finset.sum_subset hsubset
            intro i hi hnot
            simp [hnot]
      _ = ∑ i ∈ T.image tag, j i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [hi]
  exact hsum.trans (le_of_eq (himage.trans hmask.symm))
