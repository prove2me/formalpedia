-- Prove2me | solution 1 for DRLogReg.RiskEstimation.risk_two_sided_confidence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T15:25:53.592665+00:00
-- url     : https://prove2.me/submissions/fdbc8c2e-6e0c-49fc-b1a9-f6be967cdfa7

import Mathlib
import Definitions.Def_DRLogReg_RiskEstimation_Core
import Definitions.Def_DRLogReg_RiskEstimation_Risk

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace DRLogReg.RiskEstimation

theorem f135b553_classify_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

theorem f135b553_lt_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) :
    {ξ : V × Bool | sgn ξ.2 * β ξ.1 < 0} ⊆ {ξ | ξ.2 ≠ classify β ξ.1} := by
  rintro ⟨x, y⟩ h
  simp only [Set.mem_setOf_eq] at h ⊢
  have hc := f135b553_classify_iff β x
  cases y <;> simp only [sgn, Bool.false_eq_true, if_false, if_true, one_mul] at h
  · have : 0 < β x := by linarith
    intro he
    have := hc.mpr this
    rw [← he] at this
    exact Bool.false_ne_true this
  · intro he
    have := hc.mp he.symm
    linarith

theorem f135b553_sub_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) :
    {ξ : V × Bool | ξ.2 ≠ classify β ξ.1} ⊆ {ξ | sgn ξ.2 * β ξ.1 ≤ 0} := by
  rintro ⟨x, y⟩ h
  simp only [Set.mem_setOf_eq] at h ⊢
  have hc := f135b553_classify_iff β x
  cases y <;> simp only [sgn, Bool.false_eq_true, if_false, if_true, one_mul]
  · have : classify β x = true := by
      cases hcl : classify β x
      · exact absurd hcl.symm h
      · rfl
    have := hc.mp this
    linarith
  · have : classify β x = false := by
      cases hcl : classify β x
      · rfl
      · exact absurd hcl.symm h
    by_contra hne
    push_neg at hne
    have := hc.mpr hne
    rw [this] at *
    simp_all

end DRLogReg.RiskEstimation

open MeasureTheory DRLogReg.RiskEstimation in
theorem solution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (κ ε η : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hη₀ : 0 < η) (hη₁ : η ≤ 1)
    {N : ℕ} (hN : 0 < N) (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (βhat : (Fin N → V × Bool) → V →L[ℝ] ℝ)
    (hconc : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | P ∈ wassersteinBall κ ε (empirical (fun i => (ξs i).1) (fun i => (ξs i).2))}) :
    ENNReal.ofReal (1 - 2 * η) ≤ Measure.pi (fun _ : Fin N => P)
      {ξs | riskMin κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs) ≤ risk P (βhat ξs) ∧
        risk P (βhat ξs) ≤ riskMax κ ε (fun i => (ξs i).1) (fun i => (ξs i).2) (βhat ξs)} := by
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith)) (le_trans hconc ?_)
  apply measure_mono
  intro ξs hξ
  simp only [Set.mem_setOf_eq] at hξ ⊢
  constructor
  · unfold riskMin risk
    exact le_trans (iInf₂_le P hξ) (measure_mono (f135b553_lt_sub _))
  · unfold riskMax risk
    exact le_trans (measure_mono (f135b553_sub_le _)) (le_iSup₂ (f := fun Q _ => Q {ξ : V × Bool | sgn ξ.2 * (βhat ξs) ξ.1 ≤ 0}) P hξ)
