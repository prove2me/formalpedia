-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.fock_space_row_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:40.308974+00:00
-- url     : https://prove2.me/submissions/4a428b36-c268-4fae-b3d4-ba393e1ec310

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowAct
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial Formalism.REAL
noncomputable section
namespace Formalism.GradedWeylDivisibility
private lemma fockQ_eq_sum_coeff_mul_factorial_of_support_subset {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (hS : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  apply Finset.sum_subset hS
  intro m _ hm
  have h0 : f.coeff m = 0 := by
    by_contra hne
    exact hm (MvPolynomial.mem_support_iff.mpr hne)
  rw [h0]
  ring
private lemma fockQ_comm' {σ : Type*} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := by
  classical
  rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset f g (f.support ∪ g.support) Finset.subset_union_left,
    fockQ_eq_sum_coeff_mul_factorial_of_support_subset g f (f.support ∪ g.support) Finset.subset_union_right]
  exact Finset.sum_congr rfl (fun m _ => by ring)
private lemma fockQ_finset_sum_right {σ ι : Type*} (f : MvPolynomial σ ℚ) (s : Finset ι)
    (G : ι → MvPolynomial σ ℚ) : fockQ f (∑ i ∈ s, G i) = ∑ i ∈ s, fockQ f (G i) := by
  unfold fockQ
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm
private lemma fockQ_add_right' {σ : Type*} (f g₁ g₂ : MvPolynomial σ ℚ) :
    fockQ f (g₁ + g₂) = fockQ f g₁ + fockQ f g₂ := by
  unfold fockQ
  simp only [MvPolynomial.coeff_add, mul_add, add_mul, Finset.sum_add_distrib]
private lemma fockQ_add_left {σ : Type*} (f₁ f₂ g : MvPolynomial σ ℚ) :
    fockQ (f₁ + f₂) g = fockQ f₁ g + fockQ f₂ g := by
  rw [fockQ_comm', fockQ_add_right', fockQ_comm' g, fockQ_comm' g]
private lemma fockQ_C_mul_right {σ : Type*} (f g : MvPolynomial σ ℚ) (a : ℚ) :
    fockQ f (C a * g) = a * fockQ f g := by
  unfold fockQ
  simp only [MvPolynomial.coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)
private lemma fockQ_monomial_monomial {σ : Type*} [DecidableEq σ] (s t : σ →₀ ℕ) (a b : ℚ) :
    fockQ (monomial s a) (monomial t b) =
      if s = t then a * b * ((∏ k ∈ s.support, (s k).factorial : ℕ) : ℚ) else 0 := by
  classical
  by_cases ha : a = 0
  · subst ha
    simp [fockQ]
  · rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset _ _ {s} (by rw [MvPolynomial.support_monomial, if_neg ha]),
      Finset.sum_singleton, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial, if_pos rfl]
    by_cases hst : s = t
    · subst hst
      simp
    · rw [if_neg (Ne.symm hst), if_neg hst]
      ring
private lemma nonneg_of_le_add_self {σ : Type*} [DecidableEq σ] (s : σ →₀ ℕ) (v : σ) :
    (∏ k ∈ (Finsupp.single v 1 + s : σ →₀ ℕ).support, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial) =
      (s v + 1) * ∏ k ∈ s.support, (s k).factorial := by
  have key : ∀ (m : σ →₀ ℕ) (S : Finset σ), m.support ⊆ S →
      ∏ k ∈ m.support, (m k).factorial = ∏ k ∈ S, (m k).factorial := by
    intro m S hS
    apply Finset.prod_subset hS
    intro k _ hk
    have h0 : m k = 0 := by
      by_contra hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    rw [h0, Nat.factorial_zero]
  have h1 : (Finsupp.single v 1 + s : σ →₀ ℕ).support ⊆ insert v s.support := by
    intro k hk
    rw [Finsupp.mem_support_iff] at hk
    rw [Finset.mem_insert, Finsupp.mem_support_iff]
    by_cases hkv : k = v
    · exact Or.inl hkv
    · right
      simpa [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hkv] using hk
  have h2 : s.support ⊆ insert v s.support := Finset.subset_insert _ _
  rw [key _ _ h1, key s _ h2]
  have hv : v ∈ insert v s.support := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase _ _ hv, ← Finset.mul_prod_erase _ (fun k => (s k).factorial) hv]
  have h3 : ∏ k ∈ (insert v s.support).erase v, ((Finsupp.single v 1 + s : σ →₀ ℕ) k).factorial =
      ∏ k ∈ (insert v s.support).erase v, (s k).factorial := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkv : k ≠ v := Finset.ne_of_mem_erase hk
    simp [Finsupp.single_apply, Ne.symm hkv]
  rw [h3, Finsupp.add_apply, Finsupp.single_eq_same, add_comm 1 (s v), Nat.factorial_succ]
  try ring
private lemma fockQ_X_mul_monomial_eq_pderiv_monomial {σ : Type*} [DecidableEq σ] (v : σ) (s t : σ →₀ ℕ) (a b : ℚ) :
    fockQ (X v * monomial s a) (monomial t b) = fockQ (monomial s a) (pderiv v (monomial t b)) := by
  rw [X, monomial_mul, one_mul, pderiv_monomial, fockQ_monomial_monomial, fockQ_monomial_monomial]
  by_cases h : Finsupp.single v 1 + s = t
  · subst h
    have hs : Finsupp.single v 1 + s - Finsupp.single v 1 = s := add_tsub_cancel_left _ _
    rw [if_pos rfl, if_pos hs.symm, nonneg_of_le_add_self, Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  · rw [if_neg h]
    by_cases h' : s = t - Finsupp.single v 1
    · rw [if_pos h']
      have htv : t v = 0 := by
        by_contra hne
        apply h
        rw [h', add_comm]
        exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hne))
      rw [htv]
      simp
    · rw [if_neg h']
private lemma fockQ_X_mul_left_eq_pderiv_right {σ : Type*} [DecidableEq σ] (v : σ) (P Q : MvPolynomial σ ℚ) :
    fockQ (X v * P) Q = fockQ P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    induction Q using MvPolynomial.induction_on' with
    | monomial t b => exact fockQ_X_mul_monomial_eq_pderiv_monomial v s t a b
    | add q₁ q₂ h₁ h₂ => rw [map_add, fockQ_add_right', fockQ_add_right', h₁, h₂]
  | add p₁ p₂ h₁ h₂ => rw [mul_add, fockQ_add_left, fockQ_add_left, h₁, h₂]
private lemma fockQ_C_left_eq_mul_coeff_zero {σ : Type*} (a : ℚ) (Q : MvPolynomial σ ℚ) :
    fockQ (C a) Q = a * Q.coeff 0 := by
  classical
  rw [fockQ_eq_sum_coeff_mul_factorial_of_support_subset _ _ {0} (by
    rw [MvPolynomial.C_apply, MvPolynomial.support_monomial]
    split_ifs <;> simp), Finset.sum_singleton]
  simp [MvPolynomial.coeff_C]
private lemma rowAct_X_eq_sum_C_mul_X {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (v : Fin r × Fin n) :
    rowAct ℚ h (X v) = ∑ b : Fin r, C (h v.1 b) * X (b, v.2) := by
  simp [rowAct]
private lemma coeff_zero_rowAct_eq {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (Q : MvPolynomial (Fin r × Fin n) ℚ) :
    (rowAct ℚ h Q).coeff 0 = Q.coeff 0 := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [rowAct]
  | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    have hx : constantCoeff (rowAct ℚ h (X v)) = 0 := by
      rw [rowAct_X_eq_sum_C_mul_X, map_sum]
      simp
    change constantCoeff (rowAct ℚ h (p * X v)) = constantCoeff (p * X v)
    rw [map_mul, map_mul, hx, map_mul, MvPolynomial.constantCoeff_X, mul_zero, mul_zero]
set_option maxHeartbeats 800000 in

private lemma pderiv_rowAct_eq_sum_C_mul_rowAct_pderiv {r n : ℕ} (h : Matrix (Fin r) (Fin r) ℚ) (w : Fin r × Fin n)
    (Q : MvPolynomial (Fin r × Fin n) ℚ) :
    pderiv w (rowAct ℚ h Q) = ∑ c : Fin r, C (h c w.1) * rowAct ℚ h (pderiv (c, w.2) Q) := by
  induction Q using MvPolynomial.induction_on with
  | C x => simp [rowAct]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    have e1 : pderiv w (rowAct ℚ h (X v)) = if v.2 = w.2 then C (h v.1 w.1) else 0 := by
      rw [rowAct_X_eq_sum_C_mul_X, map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply]
      by_cases hv : v.2 = w.2
      · rw [if_pos hv, Finset.sum_eq_single w.1]
        · simp [Prod.ext_iff, hv]
        · intro c _ hc
          rw [if_neg (fun hh : (c, v.2) = w => hc (by rw [← hh])), mul_zero]
        · simp
      · rw [if_neg hv]
        apply Finset.sum_eq_zero
        intro c _
        rw [if_neg (fun hh : (c, v.2) = w => hv (by rw [← hh])), mul_zero]
    have e3 : ∑ c : Fin r, C (h c w.1) * (if v = (c, w.2) then (1 : MvPolynomial (Fin r × Fin n) ℚ) else 0) =
        if v.2 = w.2 then C (h v.1 w.1) else 0 := by
      by_cases hv : v.2 = w.2
      · rw [if_pos hv, Finset.sum_eq_single v.1]
        · rw [if_pos (show v = (v.1, w.2) from Prod.ext rfl hv), mul_one]
        · intro c _ hc
          rw [if_neg (fun hh : v = (c, w.2) => hc (by rw [hh])), mul_zero]
        · simp
      · rw [if_neg hv]
        apply Finset.sum_eq_zero
        intro c _
        rw [if_neg (fun hh : v = (c, w.2) => hv (by rw [hh])), mul_zero]
    have e4 : ∀ c : Fin r, rowAct ℚ h (pderiv (c, w.2) (p * X v)) =
        rowAct ℚ h p * (if v = (c, w.2) then 1 else 0) + rowAct ℚ h (X v) * rowAct ℚ h (pderiv (c, w.2) p) := by
      intro c
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_X, Pi.single_apply, map_add, map_mul, map_mul]
      split_ifs <;> simp
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hp, e1]
    simp_rw [e4]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [← e3, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun c _ => by ring)) (Finset.sum_congr rfl (fun c _ => by ring))
end Formalism.GradedWeylDivisibility
end
end

set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : FockQRowAct := by
  intro r n g P Q
  induction P using MvPolynomial.induction_on generalizing Q with
  | C a =>
    have hC : rowAct ℚ g (C a : MvPolynomial (Fin r × Fin n) ℚ) = C a := by simp [rowAct]
    rw [hC, fockQ_C_left_eq_mul_coeff_zero, fockQ_C_left_eq_mul_coeff_zero, coeff_zero_rowAct_eq]
  | add p q hp hq => rw [map_add, fockQ_add_left, fockQ_add_left, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, rowAct_X_eq_sum_C_mul_X]
    have e5 : rowAct ℚ g p * ∑ b : Fin r, C (g v.1 b) * X (b, v.2) =
        ∑ b : Fin r, C (g v.1 b) * (X (b, v.2) * rowAct ℚ g p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e5, fockQ_comm', fockQ_finset_sum_right]
    have e6 : ∀ b : Fin r, fockQ Q (C (g v.1 b) * (X (b, v.2) * rowAct ℚ g p)) =
        g v.1 b * fockQ p (rowAct ℚ g.transpose (pderiv (b, v.2) Q)) := by
      intro b
      rw [fockQ_C_mul_right, fockQ_comm', fockQ_X_mul_left_eq_pderiv_right, hp]
    rw [Finset.sum_congr rfl (fun b _ => e6 b), mul_comm p (X v), fockQ_X_mul_left_eq_pderiv_right, pderiv_rowAct_eq_sum_C_mul_rowAct_pderiv, fockQ_finset_sum_right]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [fockQ_C_mul_right, Matrix.transpose_apply]
end Formalism.GradedWeylDivisibility
