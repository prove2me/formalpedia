-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja31_original_borel_mark_count_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:01:40.906083+00:00
-- url     : https://prove2.me/submissions/6cbfa4ba-e435-42ea-9b18-c529e90b2328

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine source count of arbitrary Borel marked jumps is adapted,
as a special case of the original marked lintegral measurability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    Measurable[𝓕 T] (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let S : Set (ℝ≥0 × ℝ) := Ioc 0 T ×ˢ B
  let g : ℝ → ℝ≥0∞ := fun z => if z ∈ B then 1 else 0
  have hS : MeasurableSet S := measurableSet_Ioc.prod hB
  have hg : Measurable g := by
    dsimp [g]
    exact Measurable.ite hB measurable_const measurable_const
  have hm : Measurable[𝓕 T] (fun ω =>
      ∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂NX ω) :=
    avram_mix_gauss14_original_general_mark_lintegral_filtration_measurable
      X T g hg
  have hEq (ω : Ω) :
      NX ω S = ∫⁻ p : ℝ≥0 × ℝ,
        (if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0) ∂NX ω := by
    calc
      NX ω S = ∫⁻ p in S, (1 : ℝ≥0∞) ∂NX ω := by simp
      _ = ∫⁻ p : ℝ≥0 × ℝ,
          (if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0) ∂NX ω := by
        rw [← lintegral_indicator hS]
        apply lintegral_congr
        intro p
        by_cases ht : 0 < p.1 ∧ p.1 ≤ T
        · by_cases hb : p.2 ∈ B
          · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
          · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht, hb]
        · simp [S, g, Set.indicator, Set.mem_prod, Set.mem_Ioc, ht]
  change Measurable[𝓕 T] (fun ω => NX ω S)
  have hFun :
      (fun ω : Ω => NX ω S) =
        (fun ω => ∫⁻ p : ℝ≥0 × ℝ,
          if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂NX ω) := by
    funext ω
    exact hEq ω
  rw [hFun]
  exact hm
