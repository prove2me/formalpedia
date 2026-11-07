-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_BV_physical_residual_intrinsic_marked_cell_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:51:13.896046+00:00
-- url     : https://prove2.me/submissions/a61aef0f-662b-4b8e-8e4a-32facfe92fa3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The genuine original BV residual on every stopped physical cell is its
    drift-subtracted original increment plus the intrinsic negative-jump mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (m : ℕ)
    (W : ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let s : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
      let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i) (s (i + 1)))).map
            (fun v : ℝ≥0 => (v, Δ v)))
      (∑ i ∈ Finset.range (m + 1),
        W i ω * (R (s i) - R (s (i + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        W i ω *
          ((X.X (s (i + 1)) ω - X.X (s i) ω) -
            (((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) +
            (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal) := by
  have hCell :=
    AvramDividend.Classical.avram_bv_cell7_original_BV_raw_negative_jump_halfopen_marked_real
      X hBV
  have hAdd :=
    AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
      X hBV
  filter_upwards [hCell, hAdd] with ω hcell hadd
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let s : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0
  let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let N : ℕ → Measure (ℝ≥0 × ℝ) := fun i =>
    ((Measure.count.restrict
      ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc (s i) (s (i + 1)))).map
        (fun v : ℝ≥0 => (v, Δ v)))
  have hsmon : Monotone s := by
    simpa only [s, τ] using
      (AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
        X x D T m ω).2.2
  have hJ (i : ℕ) : J (s (i + 1)) - J (s i) =
      (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal := by
    have ha : J (s (i + 1)) = J (s i) +
        (∑' v : ℝ≥0, if s i < v ∧ v ≤ s (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) := by
      simpa only [J] using hadd (s i) (s (i + 1)) (hsmon (Nat.le_succ i))
    have hb : (∫⁻ p, ENNReal.ofReal (-p.2) ∂N i).toReal =
        (∑' v : ℝ≥0, if s i < v ∧ v ≤ s (i + 1) then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) := by
      simpa only [N, Δ] using hcell (s i) (s (i + 1))
        (hsmon (Nat.le_succ i))
    linarith only [ha, hb]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  calc
    R (s i) - R (s (i + 1)) =
        (X.X (s (i + 1)) ω - X.X (s i) ω) -
        (((s (i + 1) : ℝ) - (s i : ℝ)) * X.drift) +
        (J (s (i + 1)) - J (s i)) := by dsimp [R]; ring
    _ = _ := by rw [hJ i]
