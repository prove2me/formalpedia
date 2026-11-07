-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:26:42.6132+00:00
-- url     : https://prove2.me/submissions/2efa5405-a936-409d-bb23-503ae56208ef

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- An original stopped jump source on the *global* compensated-jump
    measure equals its intrinsic restricted source and exact physical grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        ∑ i ∈ Finset.range (m + 1),
          (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              F (v, Δ v) else 0) := by
  classical
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
      (fun v : ℝ≥0 => (v, Δ v)))
  let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
      (fun v : ℝ≥0 => (v, Δ v))
  obtain ⟨h0, hT, hGrid⟩ :=
    (AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_grid_exact_jump_time_tsum
      X x D T m ω F hF)
  have hGlobal :
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u 0) (u (m + 1)) then
            F (v, Δ v) else 0 := by
    simpa only [NX, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω (Ioc (u 0) (u (m + 1))) measurableSet_Ioc F hF)
  have hLocal :
      (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u 0) (u (m + 1)) then
            F (v, Δ v) else 0 := by
    simpa only [N, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_halfopen_physical_cell_marked_nonlinear_count_tsum
        X ω (u 0) (u (m + 1)) F hF)
  have hLink :
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) :=
    hGlobal.trans hLocal.symm
  exact ⟨h0, hT, hLink, hLink.trans hGrid⟩
