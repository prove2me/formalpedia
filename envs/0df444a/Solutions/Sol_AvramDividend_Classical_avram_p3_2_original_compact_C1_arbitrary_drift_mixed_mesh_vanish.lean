-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:32:04.254659+00:00
-- url     : https://prove2.me/submissions/ea164647-6933-4d8d-939e-d351a995feae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original raw-J variation and a compact C1 modulus make an arbitrary
physical drift-shift commutator vanish on shrinking strict-interior meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P,
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      ∀ (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
        (z c : ℕ → ℕ → ℝ),
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m → |c m i| < δ) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i))| < η := by
  filter_upwards
    [avram_p3_2_original_discounted_arbitrary_shift_mixed_J_mesh_vanish
      X hBV w q hq]
    with ω hMesh
  intro J T u n z c j hStart hEnd hGrid hBase hShift hSmall
  apply hMesh T u n z c hStart hEnd hGrid
  intro ε hε
  obtain ⟨δ, hδ, hBound⟩ :=
    avram_p3_2_uniform_compact_C1_arbitrary_physical_drift_raw_J_commutator
      w C hwC1 hOpen a b hBand ε hε
  filter_upwards [hSmall δ hδ] with m hCell
  intro i hi
  exact hBound (z m i) (c m i) (j m i)
    (hBase m i hi) (hShift m i hi) (hCell i hi)
