-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_g_original_cell_product_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:25:52.574359+00:00
-- url     : https://prove2.me/submissions/20ae174c-34a0-475f-9e06-b6918cba2d99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_finset_stable
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_g_original_prefix_product_filtration_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ 1) (k : ℕ) :
    Measurable[𝓕 t] (fun ω : Ω =>
      ∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by 
  classical
  let Jt : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω t k).toFinset
  let Js : Ω → Finset ℝ≥0 := fun ω =>
    (avram_redux19_original_strict_negative_marked_times_finite X ω s k).toFinset
  let f : Ω → ℝ≥0 → ℝ := fun ω u =>
    Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  have hMeasT : Measurable[𝓕 t] (fun ω => ∏ u ∈ Jt ω, f ω u) := by
    exact avram_route_runner_g_original_prefix_product_filtration_measurable X t k
  have hMeasS : Measurable[𝓕 t] (fun ω => ∏ u ∈ Js ω, f ω u) := by
    exact (avram_route_runner_g_original_prefix_product_filtration_measurable X s k).mono
      (𝓕.mono hst) le_rfl
  have hQuot : Measurable[𝓕 t] (fun ω =>
      (∏ u ∈ Jt ω, f ω u) / (∏ u ∈ Js ω, f ω u)) :=
    hMeasT.div hMeasS
  have hEq (ω : Ω) :
      (∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
        X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t), f ω u) =
      (∏ u ∈ Jt ω, f ω u) / (∏ u ∈ Js ω, f ω u) := by
    have hsub : Js ω ⊆ Jt ω := by
      intro u hu
      have h := (avram_redux19_original_strict_negative_marked_times_finite X ω s k).mem_toFinset.mp hu
      exact (avram_redux19_original_strict_negative_marked_times_finite X ω t k).mem_toFinset.mpr
        ⟨h.1, le_trans h.2.1 hst, h.2.2⟩
    have hdiff : Jt ω \ Js ω = (Jt ω).filter (fun u => s < u) := by
      ext u
      simp only [Finset.mem_sdiff, Finset.mem_filter]
      constructor
      · rintro ⟨hu, hn⟩
        refine ⟨hu, ?_⟩
        by_contra hh
        have hle : u ≤ s := le_of_not_gt hh
        have ht' := (avram_redux19_original_strict_negative_marked_times_finite X ω t k).mem_toFinset.mp hu
        exact hn ((avram_redux19_original_strict_negative_marked_times_finite X ω s k).mem_toFinset.mpr
          ⟨ht'.1, hle, ht'.2.2⟩)
      · rintro ⟨hu, hsu⟩
        refine ⟨hu, ?_⟩
        intro hs'
        have hs'' := (avram_redux19_original_strict_negative_marked_times_finite X ω s k).mem_toFinset.mp hs'
        exact (not_le_of_gt hsu) hs''.2.1
    have hProd := Finset.prod_sdiff (f := f ω) hsub
    rw [hdiff] at hProd
    have hNonzero : (∏ u ∈ Js ω, f ω u) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro u hu
      exact Real.exp_ne_zero _
    have hStable :=
      avram_route_runner_f_original_unit_grid_cell_finset_stable X ω s t ht k
    rw [hStable]
    apply (eq_div_iff hNonzero).2
    exact hProd
  convert hQuot using 1
  funext ω
  exact hEq ω
