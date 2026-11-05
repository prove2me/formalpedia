-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_physical_source_C1_two_errors_joint_mesh_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:00:29.538359+00:00
-- url     : https://prove2.me/submissions/a97b6759-be80-4be8-8a9b-51d3845531d6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_clock_drift_shift_mesh_vanish

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original X/D discounted drift Taylor and raw-J commutator errors jointly vanish on true refining strict-interior grids. -/
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
      ∀ (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
        (u : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ),
        let z : ℕ → ℕ → ℝ := fun m i =>
          x + X.X (u m i) ω - rightLimit D (u m i) ω
        let c : ℕ → ℕ → ℝ := fun m i =>
          ((u m (i + 1) : ℝ) - (u m i : ℝ)) * X.drift
        let j : ℕ → ℕ → ℝ := fun m i =>
          J (u m (i + 1)) - J (u m i)
        (∀ m, u m 0 = 0) →
        (∀ m, u m (n m) = T) →
        (∀ m i, i < n m → u m i ≤ u m (i + 1)) →
        (∀ δ : ℝ, 0 < δ →
          ∀ᶠ m in Filter.atTop, ∀ i, i < n m →
            (u m (i + 1) : ℝ) - (u m i : ℝ) < δ) →
        (∀ m i, i < n m →
          Set.uIcc (z m i) (z m i + c m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i - j m i) (z m i) ⊆ Set.Icc a b) →
        (∀ m i, i < n m →
          Set.uIcc (z m i + c m i - j m i)
            (z m i + c m i) ⊆ Set.Icc a b) →
        ∀ η : ℝ, 0 < η →
          ∀ᶠ m in Filter.atTop,
            |(∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i) - w (z m i) -
                  deriv w (z m i) * c m i)) +
             (∑ i ∈ Finset.range (n m),
              Real.exp (-(q * (u m i : ℝ))) *
                (w (z m i + c m i - j m i) - w (z m i + c m i) -
                  w (z m i - j m i) + w (z m i)))| < η := by
  filter_upwards
    [avram_p3_2_original_compact_C1_arbitrary_drift_mixed_mesh_vanish
      X hBV w C hwC1 hOpen a b hBand q hq] with ω hMixed
  intro J x D T u n z c j hStart hEnd hGrid hClock hTaylorBand hJumpBase hJumpShift
  have hSmall :=
    avram_p3_2_original_physical_clock_drift_shift_mesh_vanish
      X.drift u n hGrid hClock
  have hTaylor :=
    avram_p3_2_original_physical_drift_C1_Taylor_mesh_vanish
      X.drift w C hwC1 hOpen a b hBand q hq
      T u n z hStart hEnd hGrid hTaylorBand hClock
  have hJump :=
    hMixed T u n z c hStart hEnd hGrid hJumpBase hJumpShift hSmall
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  filter_upwards [hTaylor (η / 2) hη2, hJump (η / 2) hη2]
    with m hT hJ
  calc
    _ ≤
      |∑ i ∈ Finset.range (n m),
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i + c m i) - w (z m i) -
            deriv w (z m i) * c m i)| +
      |∑ i ∈ Finset.range (n m),
        Real.exp (-(q * (u m i : ℝ))) *
          (w (z m i + c m i - j m i) - w (z m i + c m i) -
            w (z m i - j m i) + w (z m i))| := abs_add_le _ _
    _ < η / 2 + η / 2 := add_lt_add hT hJ
    _ = η := by ring
