-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_zero_band_discounted_terminal_positive_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:54:12.363693+00:00
-- url     : https://prove2.me/submissions/b0e0c53c-7025-49e0-a925-b10c6ccc9833

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B ∧
         0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro S Err hErrI
  have hSource :=
    avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
      X hBV x D hD w q hq B hmono hmod T hT u huniform
  have hPos (m : ℕ) : ∀ᵐ ω ∂P, 0 ≤ Err m ω := by
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp [Err]
      split_ifs <;> positivity)
  have hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P, Err m ω ≤ ε := by
    intro ε hε
    filter_upwards [hSource ε hε] with m hm
    filter_upwards [hm] with ω hω
    by_cases hmask :
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B ∧
        (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B ∧
        0 ≤ w (x + X.X S ω - rightLimit D S ω)
    · have hu := hω hmask.1 hmask.2.1 hmask.2.2
      dsimp [Err]
      rw [if_pos hmask]
      exact max_le hu (le_of_lt hε)
    · dsimp [Err]
      rw [if_neg hmask]
      exact le_of_lt hε
  exact avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
    Err hErrI hPos hSmall
