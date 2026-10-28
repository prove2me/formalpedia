-- Prove2me | solution 1 for AvramDividend.Classical.bv_equal_halves_deficit_joint_product_law_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T12:30:46.53684+00:00
-- url     : https://prove2.me/submissions/1ebd807a-dbe0-4e4b-9978-dded204790b8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Disjoint equal-time drift-deficit increments have the same independent law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measure.map (fun ω =>
      (X.drift * (t : ℝ) - X.X t ω,
       X.drift * (t : ℝ) - (X.X (t + t) ω - X.X t ω))) P =
      (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P).prod
        (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let f : Ω → ℝ := X.X t
  let q : Ω → ℝ := fun ω => X.X (t + t) ω - X.X t ω
  let h : ℝ → ℝ := fun x => X.drift * (t : ℝ) - x
  have htt : t ≤ t + t := le_add_of_nonneg_right zero_le
  have hf : Measurable f := (X.adapted t).mono (𝓕.le t) le_rfl
  have hq : Measurable q := by
    dsimp [q]
    exact ((X.adapted (t + t)).mono (𝓕.le (t + t)) le_rfl).sub
      ((X.adapted t).mono (𝓕.le t) le_rfl)
  have hh : Measurable h := measurable_const.sub measurable_id
  have hSub : MeasurableSpace.comap f inferInstance ≤ 𝓕 t :=
    (X.adapted t).comap_le
  have hIndep : IndepFun f q P := by
    have h0 : Indep (MeasurableSpace.comap q inferInstance) (𝓕 t) P := by
      simpa only [q] using X.indepIncrements t (t + t) htt
    exact (IndepFun_iff_Indep f q P).2
      ((indep_of_indep_of_le_right h0 hSub).symm)
  have hMappedIndep : IndepFun (h ∘ f) (h ∘ q) P :=
    hIndep.comp hh hh
  have hProduct :
      Measure.map (fun ω => (h (f ω), h (q ω))) P =
        (Measure.map (h ∘ f) P).prod (Measure.map (h ∘ q) P) :=
    hMappedIndep.map_prod_eq_prod_map_map
      (hh.comp hf).aemeasurable (hh.comp hq).aemeasurable
  have hStation : IdentDistrib q f P P := by
    simpa only [q, f, add_tsub_cancel_left] using
      (X.stationaryIncrements t (t + t) htt)
  have hSame : Measure.map (h ∘ q) P = Measure.map (h ∘ f) P := by
    simpa only [h, Function.comp_def] using
      (hStation.const_sub (X.drift * (t : ℝ))).map_eq
  calc
    Measure.map (fun ω =>
      (X.drift * (t : ℝ) - X.X t ω,
       X.drift * (t : ℝ) - (X.X (t + t) ω - X.X t ω))) P =
        (Measure.map (h ∘ f) P).prod (Measure.map (h ∘ q) P) := by
          simpa only [h, f, q, Function.comp_def] using hProduct
    _ = (Measure.map (h ∘ f) P).prod (Measure.map (h ∘ f) P) := by
          rw [hSame]
    _ = (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P).prod
          (Measure.map (fun ω => X.drift * (t : ℝ) - X.X t ω) P) := by
          rfl
