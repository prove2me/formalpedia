-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_BV_discounted_terminal_one_sided_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:19.710401+00:00
-- url     : https://prove2.me/submissions/9a3df257-86ba-480f-a477-3ceedd3fe873

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
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
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop,
      ∀ᵐ ω ∂P,
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc (0 : ℝ) B →
        (x + X.X S ω - rightLimit D S ω) ∈ Icc (0 : ℝ) B →
        0 ≤ w (x + X.X S ω - rightLimit D S ω) →
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω) ≤ ε := by
  intro S ε hε
  have hSource :=
    avram_bva_a22_original_BV_uniform_terminal_one_sided_modulus
      X hBV x D hD w B hmono hmod T hT u huniform ε hε
  filter_upwards [hSource] with m hm
  filter_upwards [hm] with ω hω
  intro hy hz hwt
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
    push_cast
    linarith
  have hlast : (u m (m + 1) : ℝ) ≤ T := by
    rw [huniform m (m + 1)]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
  have hqtime : q * (u m (m + 1) : ℝ) ≤ q * T :=
    mul_le_mul_of_nonneg_left hlast hq
  have hdisc :
      Real.exp (-(q * T)) ≤
        Real.exp (-(q * (u m (m + 1) : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hqtime)
  have hdisc0 : 0 ≤ Real.exp (-(q * (u m (m + 1) : ℝ))) :=
    (Real.exp_pos _).le
  have hdisc1 : Real.exp (-(q * (u m (m + 1) : ℝ))) ≤ 1 := by
    calc
      Real.exp (-(q * (u m (m + 1) : ℝ))) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr
          (mul_nonneg hq (u m (m + 1)).property))
      _ = 1 := Real.exp_zero
  have hInc := hω hy hz
  have hscaled := mul_le_mul_of_nonneg_left hInc hdisc0
  calc
    Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) -
        Real.exp (-(q * (u m (m + 1) : ℝ))) *
          w (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ≤
      Real.exp (-(q * (u m (m + 1) : ℝ))) *
        (w (x + X.X S ω - rightLimit D S ω) -
         w (x + X.X (u m (m + 1)) ω -
           rightLimit D (u m (m + 1)) ω)) := by
          nlinarith [mul_le_mul_of_nonneg_right hdisc hwt]
    _ ≤ Real.exp (-(q * (u m (m + 1) : ℝ))) * ε := hscaled
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right hdisc1 (le_of_lt hε)
    _ = ε := one_mul _
