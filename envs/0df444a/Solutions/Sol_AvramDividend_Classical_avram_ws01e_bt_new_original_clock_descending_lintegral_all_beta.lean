-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_original_clock_descending_lintegral_all_beta
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T01:25:45.972817+00:00
-- url     : https://prove2.me/submissions/7436f5f0-079e-43f1-a47f-715a302d959f

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual original-clock descending Laplace integral has the
complete all-rate Wiener–Hopf factor, including the removable root. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam) (hroot : X.ψ lam = p) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m lam ∧
      ∀ β : ℝ, 0 < β →
        (∫⁻ z : Ω × ℝ, ENNReal.ofReal (Real.exp
          (-β * (runningSup X (Real.toNNReal z.2) z.1 -
            X.X (Real.toNNReal z.2) z.1)))
          ∂(P.prod (expMeasure p))) =
        ENNReal.ofReal
          (if β = lam then p / (lam * m)
          else (p / lam) * ((lam - β) / (p - X.ψ β))) := by
  rcases avram_ws01e_bt_new_original_clock_descending_mgf_all_beta
    X p hp lam hlam hroot with ⟨m, hm, hmDeriv, hAll⟩
  refine ⟨m, hm, hmDeriv, ?_⟩
  intro β hβ
  rw [avram_ws01e_bt_new_original_clock_descending_lintegral_eq_mgf_positive
    X p hp β hβ]
  exact congrArg ENNReal.ofReal (hAll β hβ)
