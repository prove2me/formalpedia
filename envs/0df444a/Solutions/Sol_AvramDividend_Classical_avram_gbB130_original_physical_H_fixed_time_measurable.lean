-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB130_original_physical_H_fixed_time_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T07:59:28.3556+00:00
-- url     : https://prove2.me/submissions/6bc00bac-17d6-4f0b-a6af-04a0063f4314

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ≥0) :
    Measurable[𝓕.rightCont s] (fun ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0) := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
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
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (iteratedDeriv 1 w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    iteratedDerivWithin_of_isOpen hopen
  have hc' : ContinuousOn (deriv w) (Icc a b) := by
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hsub
  have hp : Measurable (fun y : ℝ =>
      if y ∈ Icc a b then deriv w y else 1) := by
    classical
    exact hc'.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  have hYm : Measurable[𝓕.rightCont s] Y :=
    (postPaymentReserve_cadlag_adapted X x D hD.1.1).2.2 s
  have hsm : MeasurableSet[𝓕.rightCont s] {ω : Ω | s < ρ ω} := by
    convert (hρstop s).compl using 1
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff,
      WithTop.coe_le_coe, not_le]
  have ht : Measurable[𝓕.rightCont s] (fun ω => if s < ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (if Y ω ∈ Icc a b then deriv w (Y ω) else 1)
      else 0) :=
    Measurable.ite hsm (measurable_const.mul (hp.comp hYm)) measurable_const
  simpa only [Y, a, b] using ht
