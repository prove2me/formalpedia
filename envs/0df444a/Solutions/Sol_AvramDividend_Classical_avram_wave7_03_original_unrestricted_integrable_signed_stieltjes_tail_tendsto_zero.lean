-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:57:26.990944+00:00
-- url     : https://prove2.me/submissions/85e2a611-41a6-4fb2-8afa-72dccbd43c51

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine unrestricted source integrability makes the strict pre-ruin
    signed Stieltjes payment tails disappear on the actual original measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  let A : Set ℝ := paymentTimes (ruinTime X x D ω)
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ := fun t => Real.exp (-(q * t))
  have hInt' : Integrable f (μ.restrict A) := hInt
  have hSm : ∀ n : ℕ, MeasurableSet (Ioi (n : ℝ)) :=
    fun _ => measurableSet_Ioi
  have hAnti : Antitone (fun n : ℕ => Ioi (n : ℝ)) := by
    intro i j hij t ht
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact lt_of_le_of_lt hcast ht
  have hEmpty : (⋂ n : ℕ, Ioi (n : ℝ)) = (∅ : Set ℝ) := by
    ext t
    simp only [mem_iInter, mem_Ioi, mem_empty_iff_false, iff_false]
    intro ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact lt_asymm (ht n) hn
  have hTail :=
    avram_wave6_04_integrable_signed_measurable_antitone_set_tails_tendsto_zero
      (μ.restrict A) f hInt'
      (fun n : ℕ => Ioi (n : ℝ)) hSm hAnti hEmpty
  have hEq (n : ℕ) :
      (∫ t, (Ioi (n : ℝ)).indicator f t ∂(μ.restrict A)) =
      (∫ t in A ∩ Ioi (n : ℝ), f t ∂μ) := by
    rw [integral_indicator measurableSet_Ioi]
    rw [Measure.restrict_restrict measurableSet_Ioi]
    rw [inter_comm (Ioi (n : ℝ)) A]
  simpa only [A, μ, f, hEq] using hTail
