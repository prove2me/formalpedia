-- Prove2me | solution 1 for DRLogReg.RiskEstimation.worst_case_risk_confidence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T22:22:10.283929+00:00
-- url     : https://prove2.me/submissions/c20216d3-7c19-47a0-96fe-3aac548f6190

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

theorem p50f60a52_classify_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) : classify β x = true ↔ 0 < β x := by
  unfold classify condProb
  simp only [sgn, if_true, one_mul, decide_eq_true_eq, gt_iff_lt]
  have hpos : 0 < 1 + Real.exp (-(β x)) := by positivity
  rw [lt_inv_comm₀ (by norm_num) hpos]
  constructor
  · intro h
    have : Real.exp (-(β x)) < 1 := by linarith
    rw [← Real.exp_zero, Real.exp_lt_exp] at this
    linarith
  · intro h
    have : Real.exp (-(β x)) < 1 := by
      rw [← Real.exp_zero, Real.exp_lt_exp]; linarith
    norm_num
    linarith

theorem p50f60a52_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) :
    {ξ : V × Bool | ξ.2 ≠ classify β ξ.1} ⊆ {ξ | sgn ξ.2 * β ξ.1 ≤ 0} := by
  rintro ⟨x, y⟩ h
  simp only [Set.mem_setOf_eq] at h ⊢
  have hc := p50f60a52_classify_iff β x
  cases y <;> simp only [sgn, Bool.false_eq_true, if_false, if_true, one_mul]
  · have hct : classify β x = true := by
      cases hcl : classify β x
      · exact absurd hcl.symm h
      · rfl
    have := hc.mp hct
    linarith
  · have hcf : ¬ (0 < β x) := by
      intro hp
      exact h (hc.mpr hp).symm
    linarith [not_lt.mp hcf]

end DRLogReg.RiskEstimation

open MeasureTheory DRLogReg.RiskEstimation in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε η : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    {N : ℕ} (hN : 0 < N) (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (βhat : (Fin N → V × Bool) → V →L[ℝ] ℝ)
    (hconc : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | P ∈ wassersteinBall κ ε (empirical (fun i => (ξs i).1) (fun i => (ξs i).2))}) :
    ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | risk P (βhat ξs) ≤ riskMax κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs)} := by
  refine le_trans hconc ?_
  apply measure_mono
  intro ξs hξ
  simp only [Set.mem_setOf_eq] at hξ ⊢
  unfold riskMax risk
  exact le_trans (measure_mono (p50f60a52_sub _)) (le_iSup₂ (f := fun Q _ => Q {ξ : V × Bool | sgn ξ.2 * (βhat ξs) ξ.1 ≤ 0}) P hξ)
