-- Prove2me | solution 1 for AvramDividend.Classical.levy_fixed_infimum_zero_atoms_of_exp_clock_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:48:32.339499+00:00
-- url     : https://prove2.me/submissions/6415d963-c29c-411c-8ac6-74cbacdbc42d

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival
import Theorems.Thm_AvramDividend_Classical_levy_exp_clock_survival_null_fixed_horizon_ws01f
import Theorems.Thm_AvramDividend_Classical_exp_clock_Iic_strictly_positive_ws01f

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (hClockAtom : (P.prod (expMeasure p))
      {z : Ω × ℝ |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} = 0) :
    ∀ t : ℝ≥0, 0 < t →
      P {ω : Ω |
        -sInf {y : ℝ | ∃ s : ℝ≥0,
          s ≤ t ∧ y = X.X s ω} = 0} = 0 := by
  have hClockSurv : (P.prod (expMeasure p))
      {z : Ω × ℝ | ∀ s : ℝ≥0,
        s ≤ z.2.toNNReal → 0 ≤ X.X s z.1} = 0 := by
    apply le_antisymm ?_ bot_le
    calc
      (P.prod (expMeasure p))
          {z : Ω × ℝ | ∀ s : ℝ≥0,
            s ≤ z.2.toNNReal → 0 ≤ X.X s z.1} ≤
        (P.prod (expMeasure p))
          {z : Ω × ℝ |
            -sInf {y : ℝ | ∃ s : ℝ≥0,
              s ≤ z.2.toNNReal ∧ y = X.X s z.1} = 0} := by
          apply measure_mono
          intro z hz
          have hle :
              -sInf {y : ℝ | ∃ s : ℝ≥0,
                s ≤ z.2.toNNReal ∧ y = X.X s z.1} ≤ 0 :=
            (chat04_reflected_infimum_Iic_iff_survival
              X z.2.toNNReal z.1 0).mpr (by simpa using hz)
          exact le_antisymm hle
            (chat04_negative_running_infimum_nonneg X z.2.toNNReal z.1)
      _ = 0 := hClockAtom
  intro t ht
  have htReal : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hClockPos := exp_clock_Iic_strictly_positive_ws01f p (t : ℝ) hp htReal
  have hSurv :=
    levy_exp_clock_survival_null_fixed_horizon_ws01f
      X p (t : ℝ) hp hClockPos hClockSurv
  have hT : (t : ℝ).toNNReal = t := Real.toNNReal_coe
  rw [hT] at hSurv
  apply le_antisymm ?_ bot_le
  calc
    P {ω : Ω |
      -sInf {y : ℝ | ∃ s : ℝ≥0,
        s ≤ t ∧ y = X.X s ω} = 0} ≤
        P {ω : Ω | ∀ s : ℝ≥0,
          s ≤ t → 0 ≤ X.X s ω} := by
        apply measure_mono
        intro ω hz s hs
        simpa using
          ((chat04_reflected_infimum_Iic_iff_survival
            X t ω 0).mp (le_of_eq hz) s hs)
    _ = 0 := hSurv
