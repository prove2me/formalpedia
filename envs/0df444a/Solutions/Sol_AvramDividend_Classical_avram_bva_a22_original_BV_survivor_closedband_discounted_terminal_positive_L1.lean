-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_survivor_closedband_discounted_terminal_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:00:44.847571+00:00
-- url     : https://prove2.me/submissions/0b320a0e-f16d-473d-85ad-d263804a271b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
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
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (B : ℝ) (hw0 : 0 ≤ w 0)
    (hmono : MonotoneOn w (Icc (0 : ℝ) B))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ Icc (0 : ℝ) B, ∀ z ∈ Icc (0 : ℝ) B,
      |z - y| < δ → |w z - w y| < ε)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ᵐ ω ∂P, ∀ m : ℕ,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      (x + X.X (u m (m + 1)) ω -
        rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B ∧
      (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B) →
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro S Err hEnds hErrI
  have hOne :=
    avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
      X hBV x D hD w B hmono hmod T hT u huniform
  have hPos (m : ℕ) : ∀ᵐ ω ∂P, 0 ≤ Err m ω := by
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp [Err]
      split_ifs <;> positivity)
  have hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P, Err m ω ≤ ε := by
    intro ε hε
    filter_upwards [hOne ε hε] with m hm
    filter_upwards [hm, hEnds] with ω hω he
    by_cases hSurv : (S : ℝ≥0∞) < ruinTime X x D ω
    · obtain ⟨hy, hz⟩ := he m hSurv
      have hZero : (0 : ℝ) ∈ Icc (0 : ℝ) B :=
        ⟨le_refl _, le_trans hz.1 hz.2⟩
      have hwt : 0 ≤ w (x + X.X S ω - rightLimit D S ω) :=
        hw0.trans (hmono hZero hz hz.1)
      have hInc := hω hy hz
      have hden : 0 < (m : ℝ) + 2 := by positivity
      have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
        push_cast
        linarith
      have hlast : (u m (m + 1) : ℝ) ≤ T := by
        rw [huniform m (m + 1)]
        apply (div_le_iff₀ hden).2
        exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
      have hdisc :
          Real.exp (-(q * T)) ≤
            Real.exp (-(q * (u m (m + 1) : ℝ))) :=
        Real.exp_le_exp.mpr (neg_le_neg
          (mul_le_mul_of_nonneg_left hlast hq))
      have hdisc0 : 0 ≤ Real.exp (-(q * (u m (m + 1) : ℝ))) :=
        (Real.exp_pos _).le
      have hdisc1 : Real.exp (-(q * (u m (m + 1) : ℝ))) ≤ 1 := by
        calc
          Real.exp (-(q * (u m (m + 1) : ℝ))) ≤ Real.exp 0 :=
            Real.exp_le_exp.mpr (neg_nonpos.mpr
              (mul_nonneg hq (u m (m + 1)).property))
          _ = 1 := Real.exp_zero
      have hScaled := mul_le_mul_of_nonneg_left hInc hdisc0
      have hGain :
          Real.exp (-(q * T)) *
              w (x + X.X S ω - rightLimit D S ω) -
            Real.exp (-(q * (u m (m + 1) : ℝ))) *
              w (x + X.X (u m (m + 1)) ω -
                rightLimit D (u m (m + 1)) ω) ≤ ε := by
        calc
          _ ≤ Real.exp (-(q * (u m (m + 1) : ℝ))) *
            (w (x + X.X S ω - rightLimit D S ω) -
              w (x + X.X (u m (m + 1)) ω -
                rightLimit D (u m (m + 1)) ω)) := by
              nlinarith [mul_le_mul_of_nonneg_right hdisc hwt]
          _ ≤ Real.exp (-(q * (u m (m + 1) : ℝ))) * ε := hScaled
          _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hdisc1 (le_of_lt hε)
          _ = ε := one_mul _
      dsimp [Err]
      rw [if_pos hSurv]
      exact max_le hGain (le_of_lt hε)
    · dsimp [Err]
      rw [if_neg hSurv]
      exact le_of_lt hε
  exact avram_bva_a22_uniform_ae_small_positive_error_integral_vanish
    Err hErrI hPos hSmall
