-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:20:09.462339+00:00
-- url     : https://prove2.me/submissions/e1a0772d-9213-498d-83b9-e29d60c0b451

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_negative_before_horizon_iff_dense_grid
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
A controlled reserve cannot be exactly zero strictly before ruin at an arbitrary
finite stopping time. The source is the original Lévy process, on the filtration
to which the dividend strategy is adapted, with unbounded variation. The proof
derives post-stopping negative increments from source strong Markov, without
assuming conditional independence of the dividend strategy.
-/

private theorem denseCofinalSchedules :
    ∃ (times horizons : ℕ → ℝ≥0),
      (∀ a b : ℝ≥0, a < b →
        ∃ m : ℕ, a < times m ∧ times m < b) ∧
      (∀ n : ℕ, 0 < horizons n) ∧
      (∀ ε : ℝ≥0, 0 < ε →
        ∃ n : ℕ, horizons n ≤ ε) := by
  obtain ⟨times, hDense⟩ :=
    TopologicalSpace.exists_dense_seq ℝ≥0
  let horizons : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  refine ⟨times, horizons, ?_, ?_, ?_⟩
  · intro a b hab
    obtain ⟨z, ⟨n, hn⟩, hz⟩ := Dense.exists_between hDense hab
    refine ⟨n, ?_, ?_⟩
    · simpa only [← hn] using hz.1
    · simpa only [← hn] using hz.2
  · intro n
    dsimp [horizons]
    positivity
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, le_of_lt hn⟩

private theorem shiftedStoppingNegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by
  have hRegular := ae_negative_near_zero_of_unbounded_variation X hBV
  have hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by
    filter_upwards [hRegular] with ω hω
    intro n
    exact (levy_negative_before_horizon_iff_dense_grid
      X times hdense ω (horizons n)).1
      (hω (horizons n) (hpos n))
  exact levy_finiteStopping_negative_near_zero_of_grid
    X τ hτ hstop times horizons hcofinal hGridAE

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P, ((τ ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D (τ ω) ω := by
  obtain ⟨times, horizons, hdense, hpos, hcofinal⟩ :=
    denseCofinalSchedules
  have hFuture :=
    shiftedStoppingNegative X hBV τ hτ hstop times horizons
      hdense hpos hcofinal
  filter_upwards [hFuture] with ω hω
  intro hSurvive
  have hUge : 0 ≤ riskProcess X x D (τ ω) ω :=
    hPreNonneg ω (τ ω) hSurvive
  by_contra hNot
  have hZero : riskProcess X x D (τ ω) ω = 0 :=
    le_antisymm (le_of_not_gt hNot) hUge
  obtain ⟨r, hrT, hrτ⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hSurvive
  have hTr : τ ω < r := ENNReal.coe_lt_coe.mp hrT
  have hDel : 0 < r - τ ω := tsub_pos_iff_lt.mpr hTr
  obtain ⟨u, hu, hXneg⟩ := hω (r - τ ω) hDel
  have hUp : τ ω + u < r := by
    have hR : r - τ ω + τ ω = r :=
      tsub_add_cancel_of_le (le_of_lt hTr)
    linarith
  have hDmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.2.1 ω
  have hDle : D (τ ω) ω ≤ D (τ ω + u) ω :=
    hDmono (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ u))
  have hNeg : riskProcess X x D (τ ω + u) ω < 0 := by
    dsimp [riskProcess] at hZero ⊢
    linarith
  have hRuinLe : ruinTime X x D ω ≤ ((τ ω + u) : ℝ≥0∞) := by
    change (⨅ s : ℝ≥0,
      ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) ≤
      ((τ ω + u) : ℝ≥0∞)
    calc
      _ ≤ (⨅ _h : riskProcess X x D (τ ω + u) ω < 0,
          ((τ ω + u) : ℝ≥0∞)) :=
        iInf_le (fun s : ℝ≥0 =>
          ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) (τ ω + u)
      _ ≤ ((τ ω + u) : ℝ≥0∞) :=
        iInf_le (fun _h : riskProcess X x D (τ ω + u) ω < 0 =>
          ((τ ω + u) : ℝ≥0∞)) hNeg
  have hBefore : ((τ ω + u) : ℝ≥0∞) < ruinTime X x D ω :=
    lt_trans (ENNReal.coe_lt_coe.mpr hUp) hrτ
  exact (not_lt_of_ge hRuinLe) hBefore
