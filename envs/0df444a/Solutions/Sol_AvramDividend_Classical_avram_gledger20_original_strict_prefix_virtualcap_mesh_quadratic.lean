-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger20_original_strict_prefix_virtualcap_mesh_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:56:39.592667+00:00
-- url     : https://prove2.me/submissions/1876602d-7b93-4f06-b329-7b9922074814

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_top_virtualcap_source_mesh_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- All strictly preterminal original frozen-source cells satisfy the compact
    Gaussian quadratic estimate using the true prepayment prefix floor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u b L : ℝ) (hub : u < b) (hL : 0 ≤ L)
    (hwcont : ContinuousOn w (Icc u b))
    (hwderiv : ∀ y ∈ Ioo u b, HasDerivAt w (deriv w y) y)
    (hgrad : ∀ y ∈ Ico u b, 1 ≤ deriv w y)
    (hquad : ∀ y ∈ Ico u b, ∀ z ∈ Icc u b,
      w z ≤ w y + deriv w y * (z - y) + L / 2 * (z - y) ^ 2)
    (q : ℝ) (ω : Ω) (ρ : ℝ≥0)
    (hprefix : ∀ r : ℝ≥0, 0 < r → r < ρ →
      u ≤ riskProcess X x D r ω)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hclock : ∀ i ∈ S, s i ≤ t i ∧ t i < ρ) :
    let V : ℝ → ℝ := fun y => if y ≤ b then w y else w b + (y - b)
    let g : ℝ → ℝ := fun y => if y < b then deriv w y else 1
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (t i) ω - rightLimit D (s i) ω
    (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) *
      (V (Z i) - V (Y i) - g (Y i) * (Z i - Y i))) ≤
      L / 2 * (∑ i ∈ S, Real.exp (-(q * (t i : ℝ))) * (Z i - Y i) ^ 2) := by
  have hright : Monotone (fun r : ℝ≥0 => rightLimit D r ω) :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hpost : ∀ r : ℝ≥0, r < ρ →
      u ≤ x + X.X r ω - rightLimit D r ω :=
    avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω ρ u hprefix
  have hfloor : ∀ i ∈ S,
      u ≤ x + X.X (s i) ω - rightLimit D (s i) ω ∧
      u ≤ x + X.X (t i) ω - rightLimit D (s i) ω := by
    intro i hi
    obtain ⟨hsti, htρ⟩ := hclock i hi
    have hsρ : s i < ρ := lt_of_le_of_lt hsti htρ
    have hs := hpost (s i) hsρ
    have ht := hpost (t i) htρ
    have hdiv := hright hsti
    constructor
    · exact hs
    · linarith
  exact avram_gledger20_original_top_virtualcap_source_mesh_quadratic
    X x D w u b L hub hL hwcont hwderiv hgrad hquad q ω S s t hfloor
