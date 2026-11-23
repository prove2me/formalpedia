-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecText.recT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:51.385491+00:00
-- url     : https://prove2.me/submissions/ed4d2e15-a9d5-4426-8564-b34477cd92b5

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecText
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecText_geo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecText
open Finset Real
namespace Formalism.FourierDecayAlt.P.RecText
theorem _root_.solution : Formalism.FourierDecayAlt.RecursionText := by
  refine ⟨Real.exp 9, ?_⟩
  intro r a ε e σ ha0 ha1 hε hεa hra he hσ hrec
  set lam := 1 + ε + 2 * a with hlam
  set Q : ℕ → ℝ := fun k => ∏ j ∈ Icc 1 k, √(1 + e j) with hQdef
  have hQsucc : ∀ k, Q (k + 1) = Q k * √(1 + e (k + 1)) := by
    intro k; simp only [hQdef]; rw [Finset.prod_Icc_succ_top (by omega)]
  have hsq1 : ∀ j, 1 ≤ √(1 + e j) := fun j => by
    rw [Real.one_le_sqrt]; linarith [he j]
  have hQ0 : Q 0 = 1 := by simp [hQdef]
  have hQ1 : ∀ k, 1 ≤ Q k := by
    intro k; induction k with
    | zero => rw [hQ0]
    | succ k ih => rw [hQsucc]; nlinarith [hsq1 (k + 1)]
  have hQmono : Monotone Q := by
    apply monotone_nat_of_le_succ; intro k; rw [hQsucc]; nlinarith [hsq1 (k + 1), hQ1 k]
  have hlam1 : 1 ≤ lam := by linarith
  have hs0 := hσ 0
  have main : ∀ i, i ≤ r + 1 → σ i ≤ lam ^ i * Q i * σ 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hir
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0; simp [hQ0]
      · have hrec' := hrec i hpos hir
        obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        have hk : k + 1 - 1 = k := by omega
        rw [hk] at hrec'
        set M := lam ^ k * Q (k + 1) * σ 0 with hM
        have hM0 : 0 ≤ M := by
          have := pow_nonneg (by linarith : (0:ℝ) ≤ lam) k
          have := hQ1 (k + 1)
          positivity
        have hk' := ih k (by omega) (by omega)
        have h1 : (1 + ε) * √(1 + e (k + 1)) * σ k ≤ (1 + ε) * M := by
          rw [hM, hQsucc]
          have : √(1 + e (k + 1)) * σ k ≤ √(1 + e (k + 1)) * (lam ^ k * Q k * σ 0) :=
            mul_le_mul_of_nonneg_left hk' (Real.sqrt_nonneg _)
          nlinarith
        have h2 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * σ (k + 1 - t) ≤
            ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M := by
          apply Finset.sum_le_sum
          intro t ht
          rw [Finset.mem_Icc] at ht
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha0 _)
          have := ih (k + 1 - t) (by omega) (by omega)
          refine this.trans ?_
          rw [hM]
          have e1 : lam ^ (k + 1 - t) ≤ lam ^ k := pow_le_pow_right₀ hlam1 (by omega)
          have e2 : Q (k + 1 - t) ≤ Q (k + 1) := hQmono (by omega)
          have e3 : 0 ≤ lam ^ (k + 1 - t) := pow_nonneg (by linarith) _
          have e4 : 0 ≤ Q (k + 1 - t) := by linarith [hQ1 (k + 1 - t)]
          have e5 : 0 ≤ lam ^ k := pow_nonneg (by linarith) _
          have := mul_le_mul e1 e2 e4 e5
          exact mul_le_mul_of_nonneg_right this hs0
        have h3 : ∑ t ∈ Icc 2 (k + 1), a ^ (t - 1) * M ≤ 2 * a * M := by
          rw [← Finset.sum_mul]
          have := geo a ha0 ha1 (k + 1) (by omega)
          have : 0 ≤ a ^ (k + 1) := pow_nonneg ha0 _
          apply mul_le_mul_of_nonneg_right _ hM0
          linarith
        have : lam ^ (k + 1) * Q (k + 1) * σ 0 = lam * M := by rw [hM]; ring
        rw [this]
        calc σ (k + 1) ≤ (1 + ε) * M + 2 * a * M := by linarith
          _ = lam * M := by rw [hlam]; ring
  have hfin := main (r + 1) le_rfl
  have hQsq : Q (r + 1) ^ 2 = ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by
    simp only [hQdef]; rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Real.sq_sqrt]; linarith [he j]
  have hP : 0 ≤ ∏ i ∈ Icc 1 (r + 1), (1 + e i) := by rw [← hQsq]; positivity
  have hsr := hσ (r + 1)
  have step1 : σ (r + 1) ^ 2 ≤ (lam ^ (r + 1)) ^ 2 * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2 := by
    rw [← hQsq]
    have := pow_le_pow_left₀ hsr hfin 2
    calc σ (r + 1) ^ 2 ≤ (lam ^ (r + 1) * Q (r + 1) * σ 0) ^ 2 := this
      _ = _ := by ring
  set x := ((r : ℝ) + 1) * a with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx32 : x ≤ 3 / 2 := by rw [hxdef]; nlinarith
  have step2 : (lam ^ (r + 1)) ^ 2 ≤ Real.exp (6 * x) := by
    rw [← pow_mul]
    have h1 : lam ≤ Real.exp (ε + 2 * a) := by
      have := Real.add_one_le_exp (ε + 2 * a); rw [hlam]; linarith
    have h2 := pow_le_pow_left₀ (by linarith) h1 ((r + 1) * 2)
    refine h2.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have step3 : Real.exp (6 * x) ≤ 1 + Real.exp 9 * x := by
    have ht0 : 0 ≤ 2 / 3 * x := by positivity
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (9:ℝ))
      (by linarith : (0:ℝ) ≤ 1 - 2 / 3 * x) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    have : 6 * x = 2 / 3 * x * 9 := by ring
    rw [this]
    have : 0 ≤ Real.exp 9 := (Real.exp_pos 9).le
    nlinarith
  have : (lam ^ (r + 1)) ^ 2 ≤ 1 + Real.exp 9 * ((r : ℝ) + 1) * a := by
    have := step2.trans step3; rw [hxdef] at this; linarith
  refine step1.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right this hP
end Formalism.FourierDecayAlt.P.RecText
