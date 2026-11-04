-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_exact_clock_discounted_joint_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:13:24.136523+00:00
-- url     : https://prove2.me/submissions/03524e43-15b4-4063-810c-4d0cb67d86b2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A nonnegative discount rate preserves source exact-clock joint L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (n : ℕ) (μ : Measure ℝ≥0)
    (hL1 : Integrable
      (fun p : ℝ≥0 × Ω =>
        if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
          min (ruinTime X x D p.2) (n : ℝ≥0∞)
        then X.generator w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
            q * w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
        else 0) (μ.prod P)) :
    Integrable
      (fun p : ℝ≥0 × Ω =>
        Real.exp (-(q * (p.1 : ℝ))) *
          (if 0 < p.1 ∧ (p.1 : ℝ≥0∞) <
            min (ruinTime X x D p.2) (n : ℝ≥0∞)
          then X.generator w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1) -
              q * w (Function.leftLim
                (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1)
          else 0)) (μ.prod P) := by
  have hMeas : Measurable
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ)))) := by
    fun_prop
  have hBound : ∀ᵐ p : ℝ≥0 × Ω ∂(μ.prod P),
      ‖Real.exp (-(q * (p.1 : ℝ)))‖ ≤ (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro p
    have hnonneg : 0 ≤ q * (p.1 : ℝ) :=
      mul_nonneg hq (NNReal.coe_nonneg p.1)
    have hexp : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (neg_nonpos.mpr hnonneg)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hexp
  exact hL1.bdd_mul hMeas.aestronglyMeasurable hBound
