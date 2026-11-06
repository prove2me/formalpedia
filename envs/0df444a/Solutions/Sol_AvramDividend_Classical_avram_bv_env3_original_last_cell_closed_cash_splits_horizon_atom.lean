-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:12:58.545088+00:00
-- url     : https://prove2.me/submissions/012a28d9-b360-453c-8790-3abfa25e41c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original final physical-grid cell contains its right-horizon atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (_hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (a : ℝ) (ha : a < (T : ℝ)) :
    (∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes σ ∩ Ioo a (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := paymentTimes σ ∩ Ioo a (T : ℝ)
  let B : Set ℝ := paymentTimes σ ∩ {(T : ℝ)}
  have hset : paymentTimes σ ∩ Ioc a (T : ℝ) = A ∪ B := by
    ext t
    simp only [A, B, mem_inter_iff, mem_Ioc, mem_Ioo, mem_singleton_iff,
      mem_union]
    constructor
    · rintro ⟨hpay, hlo, hhi⟩
      rcases lt_or_eq_of_le hhi with hlt | heq
      · exact Or.inl ⟨hpay, hlo, hlt⟩
      · exact Or.inr ⟨hpay, heq⟩
    · rintro (⟨hpay, hlo, hhi⟩ | ⟨hpay, heq⟩)
      · exact ⟨hpay, hlo, le_of_lt hhi⟩
      · subst t
        exact ⟨hpay, ha, le_rfl⟩
  have hBm : MeasurableSet B :=
    (avram_p4_d_dividend_original_paymentTimes_measurableSet σ).inter
      (measurableSet_singleton (T : ℝ))
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro t htA htB
    have htlt : t < (T : ℝ) := htA.2.2
    have hteq : t = (T : ℝ) := htB.2
    exact (ne_of_lt htlt) hteq
  rw [hset]
  exact lintegral_union hBm hAB
