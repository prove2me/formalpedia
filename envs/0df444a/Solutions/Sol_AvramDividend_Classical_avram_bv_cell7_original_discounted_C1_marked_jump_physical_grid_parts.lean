-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_marked_jump_physical_grid_parts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:01:50.256713+00:00
-- url     : https://prove2.me/submissions/d3c229de-8b3d-4a8e-81de-c63a45b0e718

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Both signs of the true discounted stopped C1 jump source partition
    exactly on the original physical dividend grid, through contact. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) p.1 + p.2) -
          w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) p.1)
      else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) * K p)
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun i =>
    min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
  let Δ : ℝ≥0 → ℝ := fun v =>
    X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
  let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
    (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
      (fun v : ℝ≥0 => (v, Δ v))
  let K : ℝ≥0 × ℝ → ℝ := fun p =>
    if p.1 ≤ T then
      w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) p.1 + p.2) -
        w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s ω - rightLimit D s ω) p.1)
    else 0
  let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) * K p)
  have hMap : Measurable (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk measurable_snd
  have hK : Measurable K := by
    exact (AvramDividend.Classical.avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
      X x D hD w hw_cont hw_neg T).comp hMap
  have hExp : Measurable (fun p : ℝ≥0 × ℝ =>
      Real.exp (-(q * (p.1 : ℝ)))) := by fun_prop
  have hF : Measurable F := by
    exact ENNReal.measurable_ofReal.comp ((measurable_const.mul hExp).mul hK)
  exact AvramDividend.Classical.avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition
    X x D T m ω F hF
