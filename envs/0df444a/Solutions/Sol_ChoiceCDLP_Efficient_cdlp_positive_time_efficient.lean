-- Prove2me | solution 1 for ChoiceCDLP.Efficient.cdlp_positive_time_efficient
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:13:29.291849+00:00
-- url     : https://prove2.me/submissions/9c5e7a45-47bb-4fe4-8f1a-6c54154455c2

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_IsEfficient
import Definitions.Def_ChoiceCDLP_Efficient_cdlpOptimal

namespace Aux_CDLPeff

lemma auxA {n : ℕ} (f g x : Finset (Fin n) → ℝ) (T : Finset (Fin n)) (a b : ℝ) :
    ∑ S, a * (f S + b * (g S - if S = T then 1 else 0)) * x S
      = a * ∑ S, f S * x S + a * b * ∑ S, g S * x S - a * b * x T := by
  have h : ∀ S, a * (f S + b * (g S - if S = T then 1 else 0)) * x S
      = a * (f S * x S) + a * b * (g S * x S) - a * b * (if S = T then x S else 0) := by
    intro S; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun S _ => h S), Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]

lemma auxB {n : ℕ} (f g : Finset (Fin n) → ℝ) (T : Finset (Fin n)) (b : ℝ) :
    ∑ S, (f S + b * (g S - if S = T then 1 else 0)) = ∑ S, f S + b * ∑ S, g S - b := by
  have h := auxA f g (fun _ => 1) T 1 b
  simp only [one_mul, mul_one] at h
  exact h

end Aux_CDLPeff

open ChoiceCDLP.Efficient in
theorem solution {m n : ℕ} (N : ChoiceNetwork m n)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (τ : ℝ) (hτ : 0 ≤ τ)
    (t : Finset (Fin n) → ℝ) (ht : IsCDLPOptimal N lam c τ t)
    (T : Finset (Fin n)) (hT : 0 < t T) :
    IsEfficient N T := by
  rintro ⟨α, hα0, hα1, hrev, hcons⟩
  obtain ⟨⟨ht0, htc, htτ⟩, hopt⟩ := ht
  have hfeas : IsCDLPFeasible N lam c τ
      (fun S => t S + t T * (α S - if S = T then 1 else 0)) := by
    refine ⟨fun S => ?_, fun i => ?_, ?_⟩
    · show 0 ≤ t S + t T * (α S - if S = T then 1 else 0)
      by_cases hS : S = T
      · rw [if_pos hS, hS]
        nlinarith [mul_nonneg hT.le (hα0 T)]
      · rw [if_neg hS, sub_zero]
        have := mul_nonneg hT.le (hα0 S)
        linarith [ht0 S]
    · have h1 := htc i
      have h2 := hcons i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      rw [Aux_CDLPeff.auxA t α (fun S => consumption N S i) T lam (t T)]
      have e1 : ∑ S, lam * t S * consumption N S i = lam * ∑ S, t S * consumption N S i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun S _ => by ring)
      rw [e1] at h1
      have := mul_le_mul_of_nonneg_left (sub_nonpos.mpr h2) (mul_pos hlam_pos hT).le
      nlinarith
    · rw [Aux_CDLPeff.auxB, hα1]
      linarith
  have hob := hopt _ hfeas
  unfold cdlpObjective at hob
  have e2 : ∑ S, lam * revenue N S * (t S + t T * (α S - if S = T then 1 else 0))
      = ∑ S, lam * (t S + t T * (α S - if S = T then 1 else 0)) * revenue N S :=
    Finset.sum_congr rfl (fun S _ => by ring)
  have e3 : ∑ S, lam * revenue N S * t S = lam * ∑ S, t S * revenue N S := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun S _ => by ring)
  rw [e2, Aux_CDLPeff.auxA, e3] at hob
  have := mul_pos (mul_pos hlam_pos hT) (sub_pos.mpr hrev)
  nlinarith
