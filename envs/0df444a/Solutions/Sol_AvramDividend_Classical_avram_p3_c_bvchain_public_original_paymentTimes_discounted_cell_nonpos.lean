-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_public_original_paymentTimes_discounted_cell_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:33:03.164484+00:00
-- url     : https://prove2.me/submissions/ba3ed315-8ba7-4887-a499-eb65c24d4178

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The genuine stopped paymentTimes discount cell inherits the public sign. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) *
        (V (x + X.X b ω - rightLimit D b ω) -
          V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by
  have hInclude : Ioc (a : ℝ) (b : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) := by
    apply paymentTimes_Ioc_subset_of_terminal_survival
    · exact a.property
    · simpa using hPre
  have hSet : paymentTimes (ruinTime X x D ω) ∩
      Ioc (a : ℝ) (b : ℝ) = Ioc (a : ℝ) (b : ℝ) := by
    ext t
    constructor
    · intro ht
      exact ht.2
    · intro ht
      exact ⟨hInclude ht, ht⟩
  rw [hSet]
  exact avram_p3_c_bvchain_public_original_anycap_discounted_cell_nonpos
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite
      D hD ω q hq a b hab (Or.inr hPre)
