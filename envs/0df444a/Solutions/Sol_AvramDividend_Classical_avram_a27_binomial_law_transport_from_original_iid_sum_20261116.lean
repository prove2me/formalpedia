-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_binomial_law_transport_from_original_iid_sum_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:29:26.535269+00:00
-- url     : https://prove2.me/submissions/663e8065-0666-4bab-8134-f5da2c89bd85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (Y : Fin n → Ω → ℕ)
    (hMeas : ∀ i, Measurable (Y i))
    (h01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1)
    (hIndep : iIndepFun Y P)
    (p : unitInterval)
    (hP : ∀ i : Fin n, (P {ω : Ω | Y i ω = 1}).toReal = (p : ℝ))
    (Z : Ω → ℕ)
    (hZ : ∀ ω, Z ω = ∑ i : Fin n, Y i ω) :
    P.map Z = Bin(n, p) := by
  have hLaw :=
    avram_a26_iid_zero_one_finite_sum_has_binomial_law_20261116
      P n Y hMeas h01 hIndep p hP
  have hfun : Z = (fun ω : Ω => ∑ i : Fin n, Y i ω) := by
    funext ω
    exact hZ ω
  simpa only [hfun] using hLaw
