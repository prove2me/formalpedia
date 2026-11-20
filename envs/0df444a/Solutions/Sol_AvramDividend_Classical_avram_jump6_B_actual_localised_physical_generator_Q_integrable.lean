-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_localised_physical_generator_Q_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:21:34.188187+00:00
-- url     : https://prove2.me/submissions/393f2883-6f31-480c-afce-17000db7184a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0)
    (n j : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ ω i, i < (n + 1) * (j + 1) →
      let v : ℕ → ℝ≥0 := fun l =>
        min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ ω)
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      |if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
        X.generator w (Y (v i)) - q * w (Y (v i))
       else 0| ≤ B) :
    let Q : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun l =>
        min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      ∑ i ∈ Finset.range ((n + 1) * (j + 1)),
        E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
          (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
            X.generator w (Y (v i)) - q * w (Y (v i))
           else 0)
    AEStronglyMeasurable Q P → Integrable Q P := by
  intro Q hMeas
  apply Integrable.of_bound hMeas ((n : ℝ) * B)
  filter_upwards [] with ω
  let v : ℕ → ℝ≥0 := fun l =>
    min ((l : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) (σ ω)
  let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  let F : ℕ → ℝ := fun i =>
    if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
      X.generator w (Y (v i)) - q * w (Y (v i))
    else 0
  have hF' : ∀ i < (n + 1) * (j + 1), |F i| ≤ B := by
    intro i hi
    exact hF ω i hi
  have hBound :=
    avram_jump6_B_actual_stopped_physical_discounted_mesh_abs_le_horizon
      q hq n j (σ ω) (hσbound ω) B hB F hF'
  simpa [Q, F, v, Y] using hBound