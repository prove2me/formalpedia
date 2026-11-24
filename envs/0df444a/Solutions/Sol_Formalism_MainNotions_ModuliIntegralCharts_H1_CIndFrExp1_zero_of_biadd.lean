-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.zero_of_biadd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:42:49.020971+00:00
-- url     : https://prove2.me/submissions/bbee64d5-bdf4-4c59-8f70-0995997756d3

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
private theorem monoDiag_lemma_4 {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by
  rw [aeval_monomial, algebraMap_eq, monomial_eq, C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring
private theorem coeffDiag_lemma_5 {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by
  classical
  conv_lhs => rw [h.as_sum]
  rw [map_sum, coeff_sum]
  simp only [monoDiag_lemma_4, coeff_monomial]
  rw [Finset.sum_eq_single e]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb]
  · intro he
    simp only [MvPolynomial.mem_support_iff, not_not] at he
    rw [if_pos rfl, he, mul_zero]
private theorem cancel_lemma_6 {a : ℕ} (ha : a ≠ 1) {c : S} (h : (2 : S) ^ a * c = 2 * c) : c = 0 := by
  have hq : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h0
    have h1 : ((2 ^ a : ℕ) : ℚ) = ((2 : ℕ) : ℚ) := by
      push_cast
      linarith
    have h2 : 2 ^ a = 2 ^ 1 := by
      rw [pow_one]
      exact_mod_cast h1
    exact ha (Nat.pow_right_injective (le_refl 2) h2)
  have h3 : algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h
  calc c = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹ * ((2 : ℚ) ^ a - 2)) * c := by
        rw [inv_mul_cancel₀ hq, map_one, one_mul]
    _ = algebraMap ℚ S (((2 : ℚ) ^ a - 2)⁻¹) * (algebraMap ℚ S ((2 : ℚ) ^ a - 2) * c) := by
        rw [map_mul, mul_assoc]
    _ = 0 := by rw [h3, mul_zero]
private theorem prod_ite_pow_eq_two_pow_sum (k : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) :
    (e.prod fun p n => (if p.1 = k then (2 : S) else 1) ^ n) = 2 ^ (∑ i, e (k, i)) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, Fin.prod_univ_two]
  fin_cases k <;> simp [Finset.prod_pow_eq_pow_sum]
private theorem comp_lemma_9 {σ τ υ : Type} (g : σ → MvPolynomial τ S) (r : τ → MvPolynomial υ S)
    (p : MvPolynomial σ S) : aeval r (aeval g p) = aeval (fun i => aeval r (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]
private theorem aevalX_lemma_10 {σ : Type} (p : MvPolynomial σ S) : aeval X p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, aeval_X, hp]
private theorem wt_lemma_11 (e : Fin 2 × Fin d →₀ ℕ) :
    Finsupp.weight 1 e = (∑ i, e (0, i)) + ∑ i, e (1, i) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, Fin.sum_univ_two]
private theorem aeval_double_fst_of_additive {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2)) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨r, hr⟩ : ∃ r : Fin 3 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, r q = if q.1 = 2 then X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have H := congrArg (aeval r) hA1
  have e1 : aeval r (ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2)) =
      aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hr]
    rw [← two_mul]
    congr 1
  have e2 : ∀ k : Fin 3, k ≠ 2 → aeval r (ev2 h (xs S d k) (xs S d 2)) = h := by
    intro k hk
    rw [ev2, comp_lemma_9]
    conv_rhs => rw [← aevalX_lemma_10 h]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨l, i⟩
    fin_cases l <;> simp [xs, hr, hk]
  rw [e1, map_add, e2 0 (by decide), e2 1 (by decide)] at H
  exact H
private theorem aeval_double_snd_of_symm {h : MvPolynomial (Fin 2 × Fin d) S}
    (h0 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h = h + h)
    (hs : ev2 h (xs S d (1 : Fin 2)) (xs S d 0) = h) :
    aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p) h = h + h := by
  obtain ⟨G, hG⟩ : ∃ G : Fin 2 × Fin d → MvPolynomial (Fin 2 × Fin d) S,
      ∀ q, G q = if q.1 = 0 then C (2 : S) * X (1, q.2) else X (0, q.2) := ⟨_, fun _ => rfl⟩
  have e1 : aeval (fun p : Fin 2 × Fin d => C (if p.1 = 1 then (2 : S) else 1) * X p)
      (ev2 h (xs S d (1 : Fin 2)) (xs S d 0)) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e2 : ev2 (aeval (fun p : Fin 2 × Fin d => C (if p.1 = 0 then (2 : S) else 1) * X p) h)
      (xs S d (1 : Fin 2)) (xs S d 0) = aeval G h := by
    rw [ev2, comp_lemma_9]
    refine congrArg (fun f => aeval f h) ?_
    funext ⟨k, i⟩
    fin_cases k <;> simp [xs, hG]
  have e3 : ev2 (h + h) (xs S d (1 : Fin 2)) (xs S d 0) = h + h := by
    unfold ev2 at hs ⊢
    rw [map_add, hs]
  rw [hs] at e1
  rw [e1, ← e2, h0, e3]
private theorem row_degree_eq_one_of_aeval_double {h : MvPolynomial (Fin 2 × Fin d) S} (k : Fin 2)
    (hk : aeval (fun p : Fin 2 × Fin d => C (if p.1 = k then (2 : S) else 1) * X p) h = h + h)
    (e : Fin 2 × Fin d →₀ ℕ) (he : coeff e h ≠ 0) : ∑ i, e (k, i) = 1 := by
  by_contra hne
  apply he
  apply cancel_lemma_6 hne
  have H := congrArg (coeff e) hk
  rw [coeffDiag_lemma_5, prod_ite_pow_eq_two_pow_sum, coeff_add] at H
  rw [H, two_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
theorem _root_.solution {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j) (hj2 : j ≠ 2)
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) : h = 0 := by
  ext e
  rw [coeff_zero]
  by_contra he
  have h0 := row_degree_eq_one_of_aeval_double 0 (aeval_double_fst_of_additive hA1) e he
  have h1 := row_degree_eq_one_of_aeval_double 1 (aeval_double_snd_of_symm (aeval_double_fst_of_additive hA1) hs) e he
  have hw : Finsupp.weight 1 e = j := hh he
  rw [wt_lemma_11, h0, h1] at hw
  omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
