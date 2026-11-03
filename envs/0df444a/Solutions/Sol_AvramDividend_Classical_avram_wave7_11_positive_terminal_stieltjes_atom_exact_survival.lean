-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:48:44.084712+00:00
-- url     : https://prove2.me/submissions/b7661326-9e11-44eb-9c05-fe3afc416227

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_payment_iff
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The original positive endpoint Stieltjes dividend is exactly
    the discounted original dividend-measure atom if ruin is strictly later. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T)
    (hσ : ENNReal.ofReal T < σ) :
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (dividendMeasure D ω) ({T} : Set ℝ) *
        ENNReal.ofReal (Real.exp (-(q * T))) := by
  have hpay : T ∈ paymentTimes σ :=
    (avram_wave7_11_positive_horizon_endpoint_payment_iff σ T hT).mpr hσ
  have hset : (paymentTimes σ ∩ Iic T) ∩ {T} = ({T} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      exact ht.2
    · intro ht
      have htT : t = T := ht
      subst t
      exact ⟨⟨hpay, le_refl T⟩, rfl⟩
  rw [hset]
  calc
    (∫⁻ t in ({T} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({T} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * T))) ∂(dividendMeasure D ω)) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem (measurableSet_singleton T)] with t ht
          have htT : t = T := by simpa using ht
          subst t
          rfl
    _ = (dividendMeasure D ω) ({T} : Set ℝ) *
      ENNReal.ofReal (Real.exp (-(q * T))) := by
        rw [lintegral_singleton]
        exact mul_comm _ _