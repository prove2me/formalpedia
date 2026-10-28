-- Prove2me | solution 1 for AvramDividend.Classical.chat04_true_killed_scale_joint_infimum_drawdown_law_ws01a
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:10:54.299998+00:00
-- url     : https://prove2.me/submissions/67120f90-f6cf-4f81-bb8b-b89c1dbc7987

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Classical
open scoped NNReal ENNReal

/-- The actual killed q-scale expectation is the pushforward of the infimum/drawdown pair. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (x q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) :
    (∫⁻ ω : Ω,
      if ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      else (0 : ℝ≥0∞) ∂P) =
    (∫⁻ z : ℝ × ℝ,
      if z.1 ≤ x
      then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x - z.1 + z.2))
      else (0 : ℝ≥0∞)
      ∂(P.map (fun ω : Ω =>
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω},
         X.X t ω + -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})))) := by
  classical
  let L : Ω → ℝ := fun ω =>
    -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω}
  let Y : Ω → ℝ := fun ω => X.X t ω + L ω
  let F : Ω → ℝ × ℝ := fun ω => (L ω, Y ω)
  let g : ℝ × ℝ → ℝ≥0∞ := fun z =>
    if z.1 ≤ x then
      ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x - z.1 + z.2))
    else 0
  have hL : Measurable L := by
    simpa only [L] using levy_running_infimum_measurable X t
  have hSlice : Measurable (fun ω : Ω => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have hXt : Measurable (fun ω : Ω => X.X t ω) :=
    (chat04_levy_joint_time_state_measurable X).comp hSlice
  have hF : Measurable F := by
    exact hL.prodMk (hXt.add hL)
  have hWm : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hReal : Measurable (fun z : ℝ × ℝ =>
      Real.exp (-(q * (t : ℝ))) * W (x - z.1 + z.2)) :=
    measurable_const.mul (hWm.comp
      ((measurable_const.sub measurable_fst).add measurable_snd))
  have hCond : MeasurableSet {z : ℝ × ℝ | z.1 ≤ x} :=
    measurableSet_Iic.preimage measurable_fst
  have hg : Measurable g := by
    exact Measurable.ite hCond (ENNReal.measurable_ofReal.comp hReal) measurable_const
  change (∫⁻ ω : Ω,
    if ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω
    then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
    else (0 : ℝ≥0∞) ∂P) = (∫⁻ z, g z ∂(P.map F))
  rw [lintegral_map hg hF]
  apply lintegral_congr
  intro ω
  have hSurv := chat04_reflected_infimum_Iic_iff_survival X t ω x
  by_cases hs : ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω
  · have hle : L ω ≤ x := hSurv.mpr hs
    simp only [if_pos hs, g, F, if_pos hle]
    congr 1
    dsimp [Y]
    ring
  · have hnle : ¬ L ω ≤ x := by
      intro hle
      exact hs (hSurv.mp hle)
    simp only [if_neg hs, g, F, if_neg hnle]
