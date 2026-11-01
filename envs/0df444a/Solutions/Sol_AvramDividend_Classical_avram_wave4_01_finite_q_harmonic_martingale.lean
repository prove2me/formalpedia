-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_q_harmonic_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:39:52.342492+00:00
-- url     : https://prove2.me/submissions/1a887bc2-8009-4ef8-bcd4-d5c4d86b3cb7

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_finite_compensated_exponential_martingale

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (q : ℝ) (hroot : ∀ i ∈ s, X.ψ (rate i) = q) :
    Martingale
      (fun t ω => ∑ i ∈ s, coeff i *
        Real.exp (rate i * X.X t ω - (t : ℝ) * q))
      𝓕 P := by
  classical
  have hbase := avram_wave4_01_finite_compensated_exponential_martingale
    X s coeff rate hrate
  convert hbase using 1
  ext t ω
  apply Finset.sum_congr rfl
  intro i hi
  rw [hroot i hi]
