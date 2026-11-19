-- Prove2me | solution 1 for DesignTest.eq_51
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T06:24:12.857126+00:00
-- url     : https://prove2.me/submissions/725269c5-3a96-42bc-a3f6-1be3b2dd0d55

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1 / 2) (B : ℕ) (hBodd : Odd B)
    (hB : 32 / 9 * Real.log (1 / δ) ≤ (B : ℝ)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin B → Ω → ℝ) (hmeas : ∀ b, Measurable (X b))
    (hind : iIndepFun X P) (h01 : ∀ b, ∀ᵐ ω ∂P, X b ω = 0 ∨ X b ω = 1)
    (hmean : ∀ b, ∫ ω, X b ω ∂P ≤ 1 / 8) :
    P {ω | (B : ℝ) / 2 ≤ ∑ b, X b ω} ≤ ENNReal.ofReal (Real.exp (-(9 * (B : ℝ) / 32))) ∧
      Real.exp (-(9 * (B : ℝ) / 32)) ≤ δ := by
  constructor
  · set μb : Fin B → ℝ := fun b => ∫ ω, X b ω ∂P with hμb
    set Y : Fin B → Ω → ℝ := fun b ω => X b ω - μb b with hY
    have hIcc : ∀ b, ∀ᵐ ω ∂P, X b ω ∈ Set.Icc (0:ℝ) 1 := by
      intro b; filter_upwards [h01 b] with ω h
      rcases h with h | h <;> rw [h] <;> norm_num
    have hsub : ∀ b ∈ (Finset.univ : Finset (Fin B)),
        HasSubgaussianMGF (Y b) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P := by
      intro b _
      exact hasSubgaussianMGF_of_mem_Icc (hmeas b).aemeasurable (hIcc b)
    have hindY : iIndepFun Y P :=
      hind.comp (fun b x => x - μb b) (fun b => measurable_id.sub_const _)
    have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindY hsub (ε := 3 * (B : ℝ) / 8) (by positivity)
    have hc : ∑ _b : Fin B, (((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = (B : ℝ) / 4 := by
      simp; ring
    simp only [Finset.mem_univ, NNReal.coe_sum] at hH
    rw [hc] at hH
    have hBpos : (0:ℝ) < B := by
      obtain ⟨k, hk⟩ := hBodd; rw [hk]; push_cast; positivity
    have hexp : -(3 * (B : ℝ) / 8) ^ 2 / (2 * ((B : ℝ) / 4)) = -(9 * (B : ℝ) / 32) := by
      field_simp; ring
    rw [hexp] at hH
    have hsubset : {ω | (B : ℝ) / 2 ≤ ∑ b, X b ω} ⊆ {ω | 3 * (B : ℝ) / 8 ≤ ∑ b, Y b ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      simp only [hY, Finset.sum_sub_distrib]
      have : ∑ b, μb b ≤ (B : ℝ) / 8 := by
        calc ∑ b, μb b ≤ ∑ _b : Fin B, (1 / 8 : ℝ) := Finset.sum_le_sum (fun b _ => hmean b)
          _ = (B : ℝ) / 8 := by simp; ring
      linarith
    calc P {ω | (B : ℝ) / 2 ≤ ∑ b, X b ω} ≤ P {ω | 3 * (B : ℝ) / 8 ≤ ∑ b, Y b ω} :=
          measure_mono hsubset
      _ = ENNReal.ofReal (P.real {ω | 3 * (B : ℝ) / 8 ≤ ∑ b, Y b ω}) :=
          (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp (-(9 * (B : ℝ) / 32))) := ENNReal.ofReal_le_ofReal hH
  · have : Real.log (1 / δ) ≤ 9 * (B : ℝ) / 32 := by linarith
    calc Real.exp (-(9 * (B : ℝ) / 32)) ≤ Real.exp (-Real.log (1 / δ)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = δ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hδ0]
