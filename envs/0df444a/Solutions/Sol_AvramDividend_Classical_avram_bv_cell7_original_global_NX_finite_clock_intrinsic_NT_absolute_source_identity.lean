-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_cell7_original_global_NX_finite_clock_intrinsic_NT_absolute_source_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:57:35.738509+00:00
-- url     : https://prove2.me/submissions/7c49dc74-0fed-4128-bf3c-ba8512149884

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_stopped_jump_count_source_eq_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_halfopen_physical_signed_jump_count_tsum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original global marked Lévy absolute source equals its
    intrinsic finite clock mass whenever the real source vanishes after T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (f : ℝ≥0 × ℝ → ℝ) (hf : Measurable f)
    (hSupport : ∀ p : ℝ≥0 × ℝ, T < p.1 → f p = 0) :
    let Δ : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
        (fun u : ℝ≥0 => (u, Δ u)))
    let NT : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict
        ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
          (fun u : ℝ≥0 => (u, Δ u)))
    (∫⁻ p, ENNReal.ofReal |f p| ∂NX) =
      (∫⁻ p, ENNReal.ofReal |f p| ∂NT) := by
  let Δ : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) u
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0}).map
      (fun u : ℝ≥0 => (u, Δ u)))
  let NT : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict
      ({u : ℝ≥0 | 0 < u ∧ Δ u ≠ 0} ∩ Ioc 0 T)).map
        (fun u : ℝ≥0 => (u, Δ u)))
  have hF : Measurable (fun p : ℝ≥0 × ℝ => ENNReal.ofReal |f p|) :=
    hf.abs.ennreal_ofReal
  have hNX : (∫⁻ p, ENNReal.ofReal |f p| ∂NX) =
      ∑' u : ℝ≥0,
        if 0 < u ∧ Δ u ≠ 0 then ENNReal.ofReal |f (u, Δ u)| else 0 := by
    simpa only [NX, Δ, Set.mem_univ, and_true, ite_true] using
      (AvramDividend.Classical.avram_p3_2_original_stopped_jump_count_source_eq_tsum
        X ω Set.univ MeasurableSet.univ
        (fun p : ℝ≥0 × ℝ => ENNReal.ofReal |f p|) hF)
  have hNT : (∫⁻ p, ENNReal.ofReal |f p| ∂NT) =
      ∑' u : ℝ≥0,
        if (0 < u ∧ Δ u ≠ 0) ∧ u ∈ Ioc 0 T then
          ENNReal.ofReal |f (u, Δ u)| else 0 := by
    simpa only [NT, Δ] using
      (AvramDividend.Classical.avram_p3_2_original_halfopen_physical_signed_jump_count_tsum
        X ω 0 T (fun p : ℝ≥0 × ℝ => |f p|) hf.abs).1
  change (∫⁻ p, ENNReal.ofReal |f p| ∂NX) =
    (∫⁻ p, ENNReal.ofReal |f p| ∂NT)
  rw [hNX, hNT]
  apply tsum_congr
  intro u
  by_cases hj : 0 < u ∧ Δ u ≠ 0
  · by_cases huT : u ≤ T
    · simp [hj, huT, Set.mem_Ioc]
    · have hzero : f (u, Δ u) = 0 := hSupport (u, Δ u) (lt_of_not_ge huT)
      simp [hj, huT, hzero, Set.mem_Ioc]
  · simp [hj]
