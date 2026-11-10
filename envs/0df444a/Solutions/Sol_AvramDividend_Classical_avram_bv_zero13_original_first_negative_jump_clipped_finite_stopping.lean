-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_original_first_negative_jump_clipped_finite_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T11:22:47.591789+00:00
-- url     : https://prove2.me/submissions/95a531cd-8e42-49cc-b89e-d99209815e5a

import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Necessary physical stopping-clock bridge for applying original stopped
    future source laws at the first negative jump clipped by a finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) :
    let first : Ω → WithTop ℝ≥0 := fun ω =>
      ⨅ u : ℝ≥0,
        if 0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
        then (u : WithTop ℝ≥0) else ⊤
    let stop : Ω → ℝ≥0 := fun ω =>
      (min (first ω) (T : WithTop ℝ≥0)).untopD T
    (∀ ω : Ω, stop ω ≤ T) ∧
      (∀ s : ℝ≥0,
        MeasurableSet[𝓕.rightCont s]
          {ω : Ω | stop ω ≤ s}) := by
  classical
  let first : Ω → WithTop ℝ≥0 := fun ω =>
    ⨅ u : ℝ≥0,
      if 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0
      then (u : WithTop ℝ≥0) else ⊤
  let stop : Ω → ℝ≥0 := fun ω =>
    (min (first ω) (T : WithTop ℝ≥0)).untopD T
  change (∀ ω : Ω, stop ω ≤ T) ∧
    ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s]
      {ω : Ω | stop ω ≤ s}
  have hFirst : IsStoppingTime 𝓕.rightCont first :=
    avram_bv_zero13_original_first_negative_jump_inf_isStoppingTime
      X hBV hFinite
  have hClipped : IsStoppingTime 𝓕.rightCont
      (fun ω : Ω => min (first ω) (T : WithTop ℝ≥0)) :=
    hFirst.min_const T
  have hCoe (ω : Ω) :
      (stop ω : WithTop ℝ≥0) =
        min (first ω) (T : WithTop ℝ≥0) := by
    cases h : first ω with
    | top =>
        simp only [stop, h]
        rw [min_eq_right (le_top : (T : WithTop ℝ≥0) ≤ ⊤)]
        simp only [WithTop.untopD_coe]
    | coe u =>
        simp only [stop, h]
        rcases le_total u T with hle | hle
        · rw [min_eq_left (WithTop.coe_le_coe.mpr hle)]
          simp only [WithTop.untopD_coe]
        · rw [min_eq_right (WithTop.coe_le_coe.mpr hle)]
          simp only [WithTop.untopD_coe]
  constructor
  · intro ω
    apply WithTop.coe_le_coe.mp
    rw [hCoe]
    exact min_le_right _ _
  · intro s
    have hSet :
        {ω : Ω | stop ω ≤ s} =
          {ω : Ω | min (first ω) (T : WithTop ℝ≥0) ≤
            (s : WithTop ℝ≥0)} := by
      ext ω
      constructor
      · intro h
        calc
          min (first ω) (T : WithTop ℝ≥0) =
              (stop ω : WithTop ℝ≥0) := (hCoe ω).symm
          _ ≤ (s : WithTop ℝ≥0) := WithTop.coe_le_coe.mpr h
      · intro h
        change stop ω ≤ s
        apply WithTop.coe_le_coe.mp
        calc
          (stop ω : WithTop ℝ≥0) =
              min (first ω) (T : WithTop ℝ≥0) := hCoe ω
          _ ≤ (s : WithTop ℝ≥0) := h
    rw [hSet]
    exact hClipped s
