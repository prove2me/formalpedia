-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_ubv_original_controlled_preruin_fixed_time_strict_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:29:00.579764+00:00
-- url     : https://prove2.me/submissions/77cc0744-2b94-41ef-895c-06963fd01654

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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

/-- Original-source immediate downward regularity restarts after any deterministic time. -/
private theorem shiftedNegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (T : ℝ≥0)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (T + s) ω - X.X T ω < 0 := by
  let τ : Ω → ℝ≥0 := fun _ => T
  have hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) := by
    simpa only [τ] using (isStoppingTime_const 𝓕 T)
  have hτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s} := by
    intro s
    simpa only [WithTop.coe_le_coe] using hstop s
  have hRegular := ae_negative_near_zero_of_unbounded_variation X hBV
  have hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0 := by
    filter_upwards [hRegular] with ω hω
    intro n
    exact (levy_negative_before_horizon_iff_dense_grid
      X times hdense ω (horizons n)).1
      (hω (horizons n) (hpos n))
  simpa only [τ] using
    (levy_finiteStopping_negative_near_zero_of_grid
      X τ hτ hstop times horizons hcofinal hGridAE)

/-- Actual controlled reserve cannot equal zero at a fixed surviving time,
since the original UBV Levy path moves negative immediately afterwards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hPreNonneg : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω →
        0 ≤ riskProcess X x D s ω)
    (T : ℝ≥0)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < ruinTime X x D ω →
      0 < riskProcess X x D T ω := by
  have hFuture := shiftedNegative X hBV T times horizons hdense hpos hcofinal
  filter_upwards [hFuture] with ω hω
  intro hSurvive
  have hUge : 0 ≤ riskProcess X x D T ω := hPreNonneg ω T hSurvive
  by_contra hNot
  have hZero : riskProcess X x D T ω = 0 :=
    le_antisymm (le_of_not_gt hNot) hUge
  obtain ⟨r, hrT, hrτ⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hSurvive
  have hTr : T < r := ENNReal.coe_lt_coe.mp hrT
  have hDel : 0 < r - T := tsub_pos_iff_lt.mpr hTr
  obtain ⟨u, hu, hXneg⟩ := hω (r - T) hDel
  have hUp : T + u < r := by
    have hR : r - T + T = r := tsub_add_cancel_of_le (le_of_lt hTr)
    linarith
  have hDmono : Monotone (fun s : ℝ≥0 => D s ω) := hD.2.1 ω
  have hDle : D T ω ≤ D (T + u) ω := hDmono (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ u))
  have hNeg : riskProcess X x D (T + u) ω < 0 := by
    dsimp [riskProcess] at hZero ⊢
    linarith
  have hRuinLe : ruinTime X x D ω ≤ ((T + u) : ℝ≥0∞) := by
    change (⨅ s : ℝ≥0,
      ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) ≤
      ((T + u) : ℝ≥0∞)
    calc
      _ ≤ (⨅ _h : riskProcess X x D (T + u) ω < 0,
          ((T + u) : ℝ≥0∞)) :=
        iInf_le (fun s : ℝ≥0 =>
          ⨅ _h : riskProcess X x D s ω < 0, (s : ℝ≥0∞)) (T + u)
      _ ≤ ((T + u) : ℝ≥0∞) :=
        iInf_le (fun _h : riskProcess X x D (T + u) ω < 0 =>
          ((T + u) : ℝ≥0∞)) hNeg
  have hBefore : ((T + u) : ℝ≥0∞) < ruinTime X x D ω :=
    lt_trans (ENNReal.coe_lt_coe.mpr hUp) hrτ
  exact (not_lt_of_ge hRuinLe) hBefore
