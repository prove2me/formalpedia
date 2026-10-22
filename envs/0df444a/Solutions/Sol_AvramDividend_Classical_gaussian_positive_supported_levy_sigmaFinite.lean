-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_supported_levy_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:38:36.805108+00:00
-- url     : https://prove2.me/submissions/6a9c68fe-5a70-4870-871e-1e88d754c80c

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_restrict_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A positive-supported jump measure satisfying Lévy integrability
is globally sigma-finite, hence s-finite. -/
theorem solution (μ : Measure ℝ)
    (hsupport : μ (Iic (0 : ℝ)) = 0)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    SigmaFinite μ := by
  have hset :
      {a : ℝ | a ∉ Ioi (0 : ℝ)} = Iic (0 : ℝ) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_Iic, not_lt]
  have hae : ∀ᵐ z ∂μ, z ∈ Ioi (0 : ℝ) := by
    apply (ae_iff).2
    change μ {a : ℝ | a ∉ Ioi (0 : ℝ)} = 0
    rw [hset]
    exact hsupport
  have heq : μ.restrict (Ioi (0 : ℝ)) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  simpa only [heq] using
    AvramDividend.Classical.gaussian_levy_positive_restrict_sigmaFinite μ hlevy
