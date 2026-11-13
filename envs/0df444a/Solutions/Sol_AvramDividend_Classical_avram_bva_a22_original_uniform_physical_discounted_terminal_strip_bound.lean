-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:38:41.110237+00:00
-- url     : https://prove2.me/submissions/88487508-64cc-4483-940a-d52585bb55f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
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
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc c d →
      (x + X.X S ω - rightLimit D S ω) ∈ Icc c d →
      0 ≤ w (x + X.X S ω - rightLimit D S ω) →
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω) -
        Real.exp (-(q * (u m (m + 1) : ℝ))) *
        w (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ≤
      L * ((T / ((m : ℝ) + 2)) * max X.drift 0) := by
  dsimp only
  filter_upwards
    [avram_bva_a22_original_postpayment_discounted_terminal_strip_drift
      X hBV x D hD w q hq c d L hL hLip] with ω hω
  intro m hm hs hp
  let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
  have hden : 0 < (m : ℝ) + 2 := by positivity
  have hden0 : (m : ℝ) + 2 ≠ 0 := ne_of_gt hden
  have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
    push_cast
    linarith
  have hlast : u m (m + 1) ≤ S := by
    change (u m (m + 1) : ℝ) ≤ T
    rw [huniform m (m + 1)]
    apply (div_le_iff₀ hden).2
    exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
  have hgap : (S : ℝ) - (u m (m + 1) : ℝ) =
      T / ((m : ℝ) + 2) := by
    change T - (u m (m + 1) : ℝ) =
      T / ((m : ℝ) + 2)
    rw [huniform m (m + 1)]
    push_cast
    field_simp
    ring
  have hbound := hω (u m (m + 1)) S hlast hm hs hp
  change Real.exp (-(q * T)) *
      w (x + X.X S ω - rightLimit D S ω) -
      Real.exp (-(q * (u m (m + 1) : ℝ))) *
        w (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ≤
      L * ((T / ((m : ℝ) + 2)) * max X.drift 0)
  rw [hgap] at hbound
  exact hbound
