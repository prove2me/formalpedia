-- Prove2me | solution 1 for DROOptimal.Predictor.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:36:02.923144+00:00
-- url     : https://prove2.me/submissions/923c72cb-2fea-4e3f-9fad-870bbcfe8edc

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5
import Theorems.Thm_DROOptimal_Predictor_proposition_3
import Theorems.Thm_DROOptimal_Predictor_theorem_1_upper

open DROOptimal.Predictor

theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) :
    Feasible5 γ r (drPredictor γ r) := by
  have hpred := proposition_3 X hX γ hγ r hr
  refine ⟨hpred, ?_⟩
  intro x ℙ r' hr'
  set D := disappointSet γ (drPredictor γ r) x ℙ
  have hopen : IsOpen D := by
    have hc1 : Continuous (fun ℙ' : Δ d => drPredictor γ r x ℙ') :=
      hpred.comp (Continuous.prodMk continuous_const continuous_id)
    exact isOpen_lt hc1 continuous_const
  -- D ⊆ {ℙ' : r < I(ℙ', ℙ)}
  have hsub : ∀ ℙ' ∈ D, (r : EReal) ≤ relEntropy ℙ' ℙ := by
    intro ℙ' hℙ'
    by_contra hle
    rw [not_le] at hle
    have hbdd : BddAbove ((fun ℙ'' => cost γ x ℙ'') '' {ℙ'' : Δ d | relEntropy ℙ' ℙ'' ≤ (r : EReal)}) := by
      refine ⟨∑ i, |γ x i|, ?_⟩
      rintro _ ⟨Q, _, rfl⟩
      unfold cost
      apply Finset.sum_le_sum
      intro i _
      have h0 : 0 ≤ (Q : Fin d → ℝ) i := Q.2.1 i
      have h1 : (Q : Fin d → ℝ) i ≤ 1 := by
        have := Finset.single_le_sum (fun j _ => Q.2.1 j) (Finset.mem_univ i)
        rw [Q.2.2] at this; exact this
      calc (Q : Fin d → ℝ) i * γ x i ≤ (Q : Fin d → ℝ) i * |γ x i| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) h0
        _ ≤ 1 * |γ x i| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |γ x i| := one_mul _
    have hge : cost γ x ℙ ≤ drPredictor γ r x ℙ' :=
      le_csSup hbdd ⟨ℙ, hle.le, rfl⟩
    have : drPredictor γ r x ℙ' < cost γ x ℙ := hℙ'
    linarith
  have hinf : (r' : EReal) < ⨅ ℙ' ∈ D, relEntropy ℙ' ℙ :=
    lt_of_lt_of_le (by exact_mod_cast hr') (le_iInf₂ hsub)
  exact theorem_1_upper ℙ D hopen.measurableSet r' hinf
