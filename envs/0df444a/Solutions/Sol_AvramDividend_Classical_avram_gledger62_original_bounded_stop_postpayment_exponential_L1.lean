-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger62_original_bounded_stop_postpayment_exponential_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:43:55.670505+00:00
-- url     : https://prove2.me/submissions/0aff850e-c611-4791-aa06-3c1392504228

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A nonnegative original postpayment offset preserves integrability of the
    upward exponential tail of the Lévy process at a bounded stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (x : ℝ) (d : Ω → ℝ) (hd : ∀ ω, 0 ≤ d ω)
    (v : Ω → ℝ≥0)
    (hvmeas : Measurable (fun ω => (v ω : ℝ)))
    (hvstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (v ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hvbound : ∀ ω, v ω ≤ H)
    (hYmeas : AEStronglyMeasurable
      (fun ω => Real.exp (θ * (x + X.X (v ω) ω - d ω))) P) :
    Integrable (fun ω => Real.exp
      (θ * (x + X.X (v ω) ω - d ω))) P := by
  let q : ℝ := max (X.ψ θ) 0
  have hq0 : 0 ≤ q := le_max_right _ _
  have hqψ : X.ψ θ ≤ q := le_max_left _ _
  have hE : Integrable
      (fun ω => Real.exp (θ * X.X (v ω) ω - (v ω : ℝ) * q)) P :=
    avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
      X θ hθ q hqψ v hvmeas hvstop H hvbound
  let C : ℝ := Real.exp (θ * x + (H : ℝ) * q)
  have hCpos : 0 < C := Real.exp_pos _
  have hB : Integrable
      (fun ω => C * Real.exp (θ * X.X (v ω) ω - (v ω : ℝ) * q)) P :=
    hE.const_mul C
  apply Integrable.mono' hB hYmeas
  filter_upwards [] with ω
  have hv : (v ω : ℝ) ≤ (H : ℝ) := by exact_mod_cast hvbound ω
  have hdiscount : (v ω : ℝ) * q ≤ (H : ℝ) * q :=
    mul_le_mul_of_nonneg_right hv hq0
  have ht : θ * (x + X.X (v ω) ω - d ω) ≤
      θ * x + (H : ℝ) * q +
        (θ * X.X (v ω) ω - (v ω : ℝ) * q) := by
    nlinarith [mul_nonneg hθ (hd ω), hdiscount]
  have hexp := Real.exp_le_exp.mpr ht
  have heq :
      Real.exp (θ * x + (H : ℝ) * q +
        (θ * X.X (v ω) ω - (v ω : ℝ) * q)) =
      C * Real.exp (θ * X.X (v ω) ω - (v ω : ℝ) * q) := by
    rw [Real.exp_add]
  rw [heq] at hexp
  simp only [Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (θ * (x + X.X (v ω) ω - d ω))),
    abs_of_pos (mul_pos hCpos (Real.exp_pos _))]
  exact hexp
