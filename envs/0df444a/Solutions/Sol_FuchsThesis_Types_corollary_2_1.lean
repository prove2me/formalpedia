-- Prove2me | solution 1 for FuchsThesis.Types.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:38:19.811794+00:00
-- url     : https://prove2.me/submissions/ed2906c7-42e2-45ee-8a95-3d14dd9d1a20

import Mathlib
import Definitions.Def_ModernOnlineLearning_Portfolio_Types
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_FuchsThesis_Types_entropy

set_option autoImplicit false

open ModernOnlineLearning.Portfolio HolevoCQ

open FuchsThesis.Types in
theorem solution {B n : ℕ} (hn : 1 ≤ n) (p0 : Fin B → ℝ) (hp0 : p0 ∈ stdSimplex ℝ (Fin B))
    (s : Fin n → Fin B) (hs : s ∈ typeClass (T := n) p0) :
    wordProb p0 n s = Real.exp (-(n : ℝ) * entropy p0) := by
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  have hcount : ∀ b, ((Finset.univ.filter (fun t => s t = b)).card : ℝ) = n * p0 b := by
    intro b
    have h := congrFun (Finset.mem_filter.mp hs).2 b
    simp only [sequenceType] at h
    rw [← h]
    field_simp
  unfold wordProb entropy
  rw [← Finset.prod_fiberwise Finset.univ s (fun l => p0 (s l)), Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro b _
  have hinner : ∏ l ∈ Finset.univ.filter (fun l => s l = b), p0 (s l) =
      p0 b ^ (Finset.univ.filter (fun t => s t = b)).card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro l hl
    rw [(Finset.mem_filter.mp hl).2]
  rw [hinner]
  rcases (hp0.1 b).lt_or_eq with hpos | hzero
  · rw [← Real.exp_log (pow_pos hpos _), Real.log_pow, hcount b, Real.negMulLog]
    congr 1
    ring
  · have hc : ((Finset.univ.filter (fun t => s t = b)).card : ℝ) = 0 := by
      rw [hcount, ← hzero, mul_zero]
    have hc' : (Finset.univ.filter (fun t => s t = b)).card = 0 := by exact_mod_cast hc
    rw [hc', pow_zero, ← hzero, Real.negMulLog_zero, mul_zero, Real.exp_zero]
