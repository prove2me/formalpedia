-- Prove2me | solution 1 for FuchsThesis.Types.theorem_2_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:20:58.364821+00:00
-- url     : https://prove2.me/submissions/8f9fdc89-0133-48e9-9778-fdf6eb8decd2

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_GraphAlignment_Impossible_InfoMeasures
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_FuchsThesis_Types_entropy

set_option autoImplicit false

open ModernOnlineLearning.Portfolio GraphAlignment.Impossible HolevoCQ

open FuchsThesis.Types in
theorem solution {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ stdSimplex ℝ (Fin B))
    (p1 : Fin B → ℝ) (s : Fin n → Fin B) (hs : s ∈ typeClass (T := n) p1) :
    ((∀ b, 0 < p1 b → 0 < p0 b) →
      wordProb p0 n s = Real.exp (-(n : ℝ) * (entropy p1 + kl p1 p0))) ∧
    ((∃ b, 0 < p1 b ∧ p0 b = 0) → wordProb p0 n s = 0) := by
  have hseq : sequenceType s = p1 := (Finset.mem_filter.mp hs).2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp1 : ∀ b, p1 b = ((Finset.univ.filter (fun t : Fin n => s t = b)).card : ℝ) / n := by
    intro b; rw [← hseq]; rfl
  have hp1nn : ∀ b, 0 ≤ p1 b := fun b => by rw [hp1 b]; positivity
  have hwp : wordProb p0 n s =
      ∏ b, p0 b ^ (Finset.univ.filter (fun t : Fin n => s t = b)).card := by
    unfold wordProb
    rw [← Finset.prod_fiberwise' Finset.univ s p0]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    rw [Finset.prod_const]
  refine ⟨fun hsupp => ?_, fun ⟨b, hb, hb0⟩ => ?_⟩
  · rw [hwp]
    have hterm : ∀ b, -(n : ℝ) * (Real.negMulLog (p1 b) + p1 b * Real.log (p1 b / p0 b)) =
        ((Finset.univ.filter (fun t : Fin n => s t = b)).card : ℝ) * Real.log (p0 b) := by
      intro b
      have hc : ((Finset.univ.filter (fun t : Fin n => s t = b)).card : ℝ) = n * p1 b := by
        rw [hp1 b]; field_simp
      rw [hc]
      rcases (hp1nn b).lt_or_eq with h | h
      · have h0 := hsupp b h
        rw [Real.negMulLog, Real.log_div h.ne' h0.ne']
        ring
      · rw [← h]; simp
    have hsum : -(n : ℝ) * (entropy p1 + kl p1 p0) =
        ∑ b, ((Finset.univ.filter (fun t : Fin n => s t = b)).card : ℝ) * Real.log (p0 b) := by
      unfold entropy kl
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => hterm b)
    rw [hsum, Real.exp_sum]
    refine Finset.prod_congr rfl (fun b _ => ?_)
    rcases Nat.eq_zero_or_pos (Finset.univ.filter (fun t : Fin n => s t = b)).card with h | h
    · rw [h]; simp
    · have hpb : 0 < p1 b := by
        rw [hp1 b]; positivity
      rw [Real.exp_nat_mul, Real.exp_log (hsupp b hpb)]
  · rw [hwp]
    have hpos : 0 < (Finset.univ.filter (fun t : Fin n => s t = b)).card := by
      by_contra hc
      push_neg at hc
      have : (Finset.univ.filter (fun t : Fin n => s t = b)).card = 0 := by omega
      rw [hp1 b, this] at hb
      simp at hb
    apply Finset.prod_eq_zero (Finset.mem_univ b)
    rw [hb0]
    exact zero_pow (by omega)
