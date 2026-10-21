-- Prove2me | solution 1 for CorreaThreshold.Nonadaptive.cond_exp_tail_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:57:54.08553+00:00
-- url     : https://prove2.me/submissions/44796add-ae0a-4d8b-a2b1-abc8710e1182

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Setting

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} [NeZero n]
    (X : Fin n → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hXnn : ∀ i, ∀ᵐ ω ∂P, 0 ≤ X i ω)
    (hind : iIndepFun X P)
    (hcont : ∀ i, ∀ x : ℝ, P {ω | X i ω = x} = 0)
    (i : Fin n) (α : ℝ)
    (hα : P {ω | α < X i ω} = P {ω | ∀ j, X j ω ≤ X i ω}) :
    (∫⁻ ω, (if ∀ j, X j ω ≤ X i ω then
      ENNReal.ofReal (X i ω) else 0) ∂P) ≤
    (∫⁻ ω, (if α < X i ω then ENNReal.ofReal (X i ω) else 0) ∂P) := by
  classical
  set A : Set Ω := {ω | ∀ j, X j ω ≤ X i ω} with hAdef
  set B : Set Ω := {ω | α < X i ω} with hBdef
  have hA : MeasurableSet A := by
    have : A = ⋂ j, {ω | X j ω ≤ X i ω} := by
      ext ω; simp [hAdef]
    rw [this]
    exact MeasurableSet.iInter fun j => measurableSet_le (hXm j) (hXm i)
  have hB : MeasurableSet B := measurableSet_lt measurable_const (hXm i)
  have hf : Measurable (fun ω => ENNReal.ofReal (X i ω)) := (hXm i).ennreal_ofReal
  have e1 : (∫⁻ ω, (if ∀ j, X j ω ≤ X i ω then ENNReal.ofReal (X i ω) else 0) ∂P)
      = ∫⁻ ω in A, ENNReal.ofReal (X i ω) ∂P := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro ω
    simp [Set.indicator_apply, hAdef]
  have e2 : (∫⁻ ω, (if α < X i ω then ENNReal.ofReal (X i ω) else 0) ∂P)
      = ∫⁻ ω in B, ENNReal.ofReal (X i ω) ∂P := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro ω
    simp [Set.indicator_apply, hBdef]
  rw [e1, e2]
  have h1 := lintegral_inter_add_diff (μ := P) (fun ω => ENNReal.ofReal (X i ω)) A hB
  have h2 := lintegral_inter_add_diff (μ := P) (fun ω => ENNReal.ofReal (X i ω)) B hA
  rw [Set.inter_comm B A] at h2
  have hm1 : ∫⁻ ω in A \ B, ENNReal.ofReal (X i ω) ∂P ≤ ENNReal.ofReal α * P (A \ B) := by
    calc ∫⁻ ω in A \ B, ENNReal.ofReal (X i ω) ∂P
        ≤ ∫⁻ ω in A \ B, ENNReal.ofReal α ∂P := by
          apply setLIntegral_mono measurable_const
          intro ω hω
          have : ¬ (α < X i ω) := hω.2
          exact ENNReal.ofReal_le_ofReal (not_lt.1 this)
      _ = ENNReal.ofReal α * P (A \ B) := by rw [setLIntegral_const]
  have hm2 : ENNReal.ofReal α * P (B \ A) ≤ ∫⁻ ω in B \ A, ENNReal.ofReal (X i ω) ∂P := by
    calc ENNReal.ofReal α * P (B \ A) = ∫⁻ ω in B \ A, ENNReal.ofReal α ∂P := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ ω in B \ A, ENNReal.ofReal (X i ω) ∂P := by
          apply setLIntegral_mono hf
          intro ω hω
          exact ENNReal.ofReal_le_ofReal (le_of_lt hω.1)
  have hP1 := measure_inter_add_diff (μ := P) A hB
  have hP2 := measure_inter_add_diff (μ := P) B hA
  rw [Set.inter_comm B A] at hP2
  have hPeq : P (A \ B) = P (B \ A) := by
    have : P (A ∩ B) + P (A \ B) = P (A ∩ B) + P (B \ A) := by
      rw [hP1, hP2]; exact hα.symm
    exact (ENNReal.add_right_inj (measure_ne_top P _)).1 this
  have hmain : ∫⁻ ω in A \ B, ENNReal.ofReal (X i ω) ∂P ≤ ∫⁻ ω in B \ A, ENNReal.ofReal (X i ω) ∂P := by
    calc ∫⁻ ω in A \ B, ENNReal.ofReal (X i ω) ∂P ≤ ENNReal.ofReal α * P (A \ B) := hm1
      _ = ENNReal.ofReal α * P (B \ A) := by rw [hPeq]
      _ ≤ _ := hm2
  rw [← h1, ← h2]
  exact add_le_add le_rfl hmain
