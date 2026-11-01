-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_02_source_localtime_every_cap_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T09:41:09.855001+00:00
-- url     : https://prove2.me/submissions/a9633b79-3c0a-46fc-b5d0-3a31658394f4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Infinite negative-jump first variation makes every positive finite-time
running-supremum record level accessible with positive source probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) (b : ℝ) :
    0 < P {ω : Ω | b < runningSup X t ω} := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have htreal : 0 < (t : ℝ) := by exact_mod_cast ht
  obtain ⟨β, hβ1, hβθ⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv 0 le_rfl
      (b / (t : ℝ))
  have hβpos : 0 < β := lt_of_lt_of_le one_pos hβ1
  have hLap := X.laplace t β hβpos.le
  have hMoment :
      (∫ ω, Real.exp (β * X.X t ω) ∂P) =
        Real.exp ((t : ℝ) * X.ψ β) := by
    have h := hLap.2
    change (∫ ω, Real.exp (β * X.X t ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ β) at h
    exact h
  have hψ : (b / (t : ℝ)) * β < X.ψ β := by
    simpa using (hβθ β le_rfl)
  have hmult : ((b / (t : ℝ)) * β) * (t : ℝ) = b * β := by
    field_simp [ne_of_gt htreal]
  have hψt : b * β < (t : ℝ) * X.ψ β := by
    calc
      b * β = ((b / (t : ℝ)) * β) * (t : ℝ) := hmult.symm
      _ < X.ψ β * (t : ℝ) := mul_lt_mul_of_pos_right hψ htreal
      _ = (t : ℝ) * X.ψ β := mul_comm _ _
  have hPositive : 0 < P {ω : Ω | b < X.X t ω} := by
    by_contra hNotPositive
    have hZero : P {ω : Ω | b < X.X t ω} = 0 :=
      bot_unique (not_lt.mp hNotPositive)
    have hLe : ∀ᵐ ω ∂P, X.X t ω ≤ b := by
      have hAE : ∀ᵐ ω ∂P, ¬ b < X.X t ω := by
        exact (ae_iff).2 (by simpa using hZero)
      filter_upwards [hAE] with ω hw
      exact le_of_not_gt hw
    have hBound : ∀ᵐ ω ∂P,
        Real.exp (β * X.X t ω) ≤ Real.exp (β * b) := by
      filter_upwards [hLe] with ω hw
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw hβpos.le)
    have hIntLe :
        (∫ ω, Real.exp (β * X.X t ω) ∂P) ≤ Real.exp (β * b) := by
      calc
        _ ≤ ∫ _ : Ω, Real.exp (β * b) ∂P :=
          integral_mono_ae hLap.1 (integrable_const _) hBound
        _ = Real.exp (β * b) := by simp
    rw [hMoment] at hIntLe
    have hExpGt :
        Real.exp (β * b) < Real.exp ((t : ℝ) * X.ψ β) := by
      exact Real.exp_lt_exp.mpr (by nlinarith [hψt])
    exact (not_le_of_gt hExpGt) hIntLe
  have hIncl :
      {ω : Ω | b < X.X t ω} ⊆
        {ω : Ω | b < runningSup X t ω} := by
    intro ω hw
    exact lt_of_lt_of_le hw ((runningSup_monotone_and_path_le X ω).2 t)
  exact lt_of_lt_of_le hPositive (measure_mono hIncl)
