-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T00:26:42.258314+00:00
-- url     : https://prove2.me/submissions/24cf2ba6-ff22-49c2-b619-701934ab5d9f

import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
import Theorems.Thm_AvramDividend_Classical_avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Nat
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) (n + 1) : ℝ) ∂P) =
        (r : ℝ) * (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) := by
  have hLaw :=
    avram_a27_source_original_negative_Borel_count_HasLaw_of_true_count_20261118
      X hFinite T B hB hNeg K hK hCount r hr
  have hTransfer (m : ℕ) :
      (∫ ω, (Nat.descFactorial (K ω) m : ℝ) ∂P) =
      (∫ k : ℕ, (Nat.descFactorial k m : ℝ) ∂poissonMeasure r) := by
    have hMeas : Measurable (fun k : ℕ => (Nat.descFactorial k m : ℝ)) :=
      measurable_of_countable _
    simpa only [Function.comp_def] using
      (hLaw.integral_comp hMeas.aestronglyMeasurable)
  intro n
  rw [hTransfer (n + 1), hTransfer n]
  exact avram_a25_poisson_source_free_descFactorial_moment_recurrence_20261118 r n
