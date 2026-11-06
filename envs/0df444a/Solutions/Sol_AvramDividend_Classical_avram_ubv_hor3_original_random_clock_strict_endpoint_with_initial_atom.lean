-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_random_clock_strict_endpoint_with_initial_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:23:54.957121+00:00
-- url     : https://prove2.me/submissions/61b5f255-b79d-4a81-9825-ad8961647289

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_zero_eq_singleton_zero
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_eq_inter_Iio_of_pos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ)
    (hτ : ∀ ω, 0 ≤ τ ω) (q T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal (τ ω))) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ (Iio (τ ω) ∪ {0})) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  have hZeroSet (σ : ℝ≥0∞) :
      paymentTimes σ ∩ (Iio (0 : ℝ) ∪ {0}) = ({0} : Set ℝ) := by
    ext t
    constructor
    · intro ht
      rcases ht.2 with htNeg | htZero
      · have hNonneg : (0 : ℝ) ≤ t := ht.1.1
        exact (False.elim (not_lt_of_ge hNonneg htNeg))
      · exact htZero
    · intro ht
      rcases ht with rfl
      simp [paymentTimes]
  have hBase (σ : ℝ≥0∞) (s : ℝ) (hs : 0 ≤ s) :
      paymentTimes (min σ (ENNReal.ofReal s)) =
        paymentTimes σ ∩ (Iio s ∪ {0}) := by
    rcases eq_or_lt_of_le hs with hsZero | hsPos
    · subst s
      calc
        paymentTimes (min σ (ENNReal.ofReal (0 : ℝ))) =
            ({0} : Set ℝ) := by
              simpa using paymentTimes_min_zero_eq_singleton_zero σ
        _ = paymentTimes σ ∩ (Iio (0 : ℝ) ∪ {0}) := (hZeroSet σ).symm
    · have hUnion : Iio s ∪ {0} = Iio s := by
        ext t
        constructor
        · intro ht
          rcases ht with htLt | htZero
          · exact htLt
          · have htEq : t = 0 := htZero
            subst t
            exact hsPos
        · intro ht
          exact Or.inl ht
      rw [hUnion]
      exact paymentTimes_min_ofReal_eq_inter_Iio_of_pos σ s hsPos
  have hSet (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal (τ ω))) ∩ Iic T =
        (paymentTimes (ruinTime X x D ω) ∩ (Iio (τ ω) ∪ {0})) ∩ Iic T := by
    exact congrArg (fun S : Set ℝ => S ∩ Iic T)
      (hBase (ruinTime X x D ω) (τ ω) (hτ ω))
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal (τ ω))) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ (Iio (τ ω) ∪ {0})) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [hSet ω]
  simp_rw [hCash]
