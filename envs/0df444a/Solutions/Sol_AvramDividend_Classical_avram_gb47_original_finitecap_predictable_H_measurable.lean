-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb47_original_finitecap_predictable_H_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:32:01.730933+00:00
-- url     : https://prove2.me/submissions/115db9ec-c5f5-4dcf-9b18-b8761a769218

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Each stopped Hessian grid coefficient is measurable in the original
filtration using adaptation and the post-payment dividend right limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let H : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then (1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then iteratedDeriv 2 w Y else 0)
      else 0
    ∀ m i, Measurable (H m i) := by
  intro H m i
  let s : ℝ≥0 := (i : ℝ≥0) *
    ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let Y : Ω → ℝ := fun ω => x + X.X s ω - rightLimit D s ω
  have hcap : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hfrac : (((j + 1 : ℕ) : ℝ) /
      ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (show j + 1 < j + 2 by omega)
  have hb : b < C.toReal := by
    dsimp [b]
    nlinarith [mul_lt_mul_of_pos_left hfrac hcap]
  have hsub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have ha : 0 < a := by dsimp [a]; positivity
    have hy0 : 0 ≤ y := le_trans (le_of_lt ha) hy.1
    refine ⟨lt_of_lt_of_le ha hy.1, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 hFiniteCap).2
      (lt_of_le_of_lt hy.2 hb)
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hopen.uniqueDiffOn
  have hc : ContinuousOn
      (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn
      (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (iteratedDeriv 2 w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    iteratedDerivWithin_of_isOpen hopen
  have hc' : ContinuousOn (iteratedDeriv 2 w) (Icc a b) :=
    (hc.congr heq.symm).mono hsub
  have hp : Measurable (fun y : ℝ =>
      if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by
    classical
    exact hc'.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  have hXm : Measurable (X.X s) :=
    (X.adapted s).mono (𝓕.le s) le_rfl
  have hDm : Measurable (fun ω => rightLimit D s ω) :=
    dividendStrategy_rightLimit_measurable D hD.1.1 s
  have hYm : Measurable Y :=
    (measurable_const.add hXm).sub hDm
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hsm : MeasurableSet {ω : Ω | s < ρ ω} := by
    have hm : MeasurableSet {ω : Ω |
        (s : WithTop ℝ≥0) < (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρm
    simpa only [WithTop.coe_lt_coe] using hm
  have ht : Measurable (fun ω => if s < ρ ω then
      (1 / 2 : ℝ) * Real.exp (-(q * (s : ℝ))) *
        (if Y ω ∈ Icc a b then iteratedDeriv 2 w (Y ω) else 0)
      else 0) :=
    Measurable.ite hsm (measurable_const.mul (hp.comp hYm)) measurable_const
  simpa only [H, Y, s, a, b] using ht
