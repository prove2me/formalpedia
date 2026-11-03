-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:51:15.388647+00:00
-- url     : https://prove2.me/submissions/89cf1f5a-ecd0-44e5-afe0-baa0fdd38dd1

import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At zero real horizon the exact original Stieltjes payment consists of
    the time-zero dividend atom, regardless of the ruin clock. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q : ℝ) :
    (∫⁻ t in paymentTimes σ ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (dividendMeasure D ω) ({0} : Set ℝ) := by
  have hset : paymentTimes σ ∩ Iic (0 : ℝ) = ({0} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      have hnonneg : 0 ≤ t := ht.1.1
      have hle : t ≤ 0 := ht.2
      exact le_antisymm hle hnonneg
    · intro ht
      change t = 0 at ht
      subst t
      simp [paymentTimes]
  rw [hset]
  calc
    (∫⁻ t in ({0} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({0} : Set ℝ),
        (1 : ℝ≥0∞) ∂(dividendMeasure D ω)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (measurableSet_singleton (0 : ℝ))] with t ht
        have ht0 : t = 0 := by simpa using ht
        subst t
        simp
    _ = (dividendMeasure D ω) ({0} : Set ℝ) := by simp
