-- Prove2me | solution 1 for EditMulticoloring.Code.polynomial_coloring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T09:39:41.922337+00:00
-- url     : https://prove2.me/submissions/96d2c5a2-3571-4dc2-9e75-a2b0a1126df7

import Mathlib
import Definitions.Def_EditMulticoloring_Code_Graph

section
set_option autoImplicit false
namespace EditMulticoloring.Dev.PolyColoring
open EditMulticoloring.Code

lemma fieldElement_eq {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q) (hQ : 0 < Q) (a : ℕ) :
    fieldElement e a = e.symm ⟨a % Q, Nat.mod_lt _ hQ⟩ := by
  unfold fieldElement
  rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using Nat.mod_lt _ hQ)]
  simp

lemma coeff_idPoly {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q) (K id j : ℕ) :
    (identifierPoly e K id).coeff j = if j < K then fieldElement e (id / Q ^ j) else 0 := by
  unfold identifierPoly
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp [Finset.sum_ite_eq']

lemma digits_inj (Q : ℕ) (hQ : 0 < Q) : ∀ (K n m : ℕ), n < Q ^ K → m < Q ^ K →
    (∀ j < K, n / Q ^ j % Q = m / Q ^ j % Q) → n = m := by
  intro K
  induction K with
  | zero => intro n m hn hm _; simp at hn hm; omega
  | succ K ih =>
    intro n m hn hm h
    have h0 := h 0 (by omega)
    simp only [pow_zero, Nat.div_one] at h0
    have : n / Q = m / Q := by
      apply ih
      · rw [Nat.div_lt_iff_lt_mul hQ]; rwa [pow_succ] at hn
      · rw [Nat.div_lt_iff_lt_mul hQ]; rwa [pow_succ] at hm
      · intro j hj
        have := h (j + 1) (by omega)
        rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    have h1 := Nat.div_add_mod n Q
    have h2 := Nat.div_add_mod m Q
    rw [this, h0] at h1
    omega

lemma idPoly_inj {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q) (hQ : 0 < Q) (K a b : ℕ)
    (ha : a < Q ^ K) (hb : b < Q ^ K)
    (h : identifierPoly e K a = identifierPoly e K b) : a = b := by
  apply digits_inj Q hQ K a b ha hb
  intro j hj
  have := congrArg (fun p => p.coeff j) h
  simp only [coeff_idPoly, hj, if_true, fieldElement_eq e hQ] at this
  have := e.symm.injective this
  exact congrArg Fin.val this

lemma natDegree_sub_lt {F : Type} [Field F] {Q : ℕ} (e : F ≃ Fin Q) (K a b : ℕ) (hK : 1 ≤ K) :
    (identifierPoly e K a - identifierPoly e K b).natDegree ≤ K - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Polynomial.coeff_sub, coeff_idPoly, coeff_idPoly]
  have : ¬ N < K := by omega
  simp [this]

lemma exists_sep {V F : Type} [Fintype V] [Field F] {Q : ℕ}
    (G : SimpleGraph V) (e : F ≃ Fin Q) (r K : ℕ) (hK : 1 ≤ K) (hQ : r * K + 1 ≤ Q)
    (degree : ∀ v, (neighbors G v).card ≤ r)
    (id : V → ℕ) (hid : Function.Injective id) (range : ∀ v, id v < Q ^ K) (v : V) :
    ∃ a : F, Separates G e K id v a := by
  classical
  haveI : Fintype F := Fintype.ofEquiv (Fin Q) e.symm
  have hcard : Fintype.card F = Q := by simpa using Fintype.card_congr e
  let S : Finset F := (neighbors G v).biUnion
    (fun u => (identifierPoly e K (id v) - identifierPoly e K (id u)).roots.toFinset)
  have hS : S.card ≤ r * (K - 1) := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (K - 1) ?_).trans ?_
    · intro u hu
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (natDegree_sub_lt e K _ _ hK))
    · simpa [mul_comm] using Nat.mul_le_mul_right (K - 1) (degree v)
  have hlt : S.card < Fintype.card F := by
    rw [hcard]
    have : r * (K - 1) ≤ r * K := Nat.mul_le_mul_left _ (by omega)
    omega
  obtain ⟨a, haS⟩ : ∃ a, a ∉ S := by
    by_contra h
    push_neg at h
    have : S = Finset.univ := Finset.eq_univ_of_forall h
    rw [this, Finset.card_univ] at hlt
    exact lt_irrefl _ hlt
  refine ⟨a, fun u hu heq => haS ?_⟩
  have hne : id v ≠ id u := fun h => (G.ne_of_adj hu) (hid h)
  have hQ0 : 0 < Q := by omega
  have hpne : identifierPoly e K (id v) - identifierPoly e K (id u) ≠ 0 := by
    intro h0
    exact hne (idPoly_inj e hQ0 K _ _ (range v) (range u) (sub_eq_zero.1 h0))
  simp only [S, Finset.mem_biUnion, Multiset.mem_toFinset]
  refine ⟨u, by simpa [neighbors] using hu, ?_⟩
  rw [Polynomial.mem_roots hpne]
  simp [Polynomial.IsRoot, heq]

lemma find_spec {F : Type} (l : List F) (p : F → Bool) (d : F) (h : ∃ a ∈ l, p a = true) :
    p ((l.find? p).getD d) = true := by
  obtain ⟨a, ha, hpa⟩ := h
  cases hf : l.find? p with
  | none => rw [List.find?_eq_none] at hf; simpa [hpa] using hf a ha
  | some b => simpa using List.find?_some hf

lemma first_sep {V F : Type} [Fintype V] [Field F] {Q : ℕ}
    (G : SimpleGraph V) (e : F ≃ Fin Q) (K : ℕ) (id : V → ℕ) (v : V)
    (h : ∃ a : F, Separates G e K id v a) :
    Separates G e K id v (firstSeparating G e K id v) := by
  classical
  obtain ⟨a, ha⟩ := h
  have := find_spec (((List.finRange Q).map e.symm)) (fun a => decide (Separates G e K id v a)) 0
    ⟨a, by simpa using ⟨e a, by simp⟩, by simpa using ha⟩
  simpa [firstSeparating] using this

end EditMulticoloring.Dev.PolyColoring

namespace EditMulticoloring.Code
open EditMulticoloring.Dev.PolyColoring in
theorem chk_polynomial_coloring {V F : Type} [Fintype V] [Field F]
    (G : SimpleGraph V) (r K : ℕ) (hr : 1 ≤ r) (hK : 1 ≤ K)
    (degree : ∀ v, (neighbors G v).card ≤ r)
    (id : V → ℕ) (hid : Function.Injective id) (range : ∀ v, id v < 2 ^ K)
    (e : F ≃ Fin (fieldSize r K)) :
    (∀ v, ∃ a : F, Separates G e K id v a) ∧
    (∀ v, Separates G e K id v (firstSeparating G e K id v)) ∧
    (∀ v, polynomialColor G e K id v < (fieldSize r K) ^ 2) ∧
    (∀ u v, G.Adj u v → polynomialColor G e K id u ≠ polynomialColor G e K id v)
    := by
  have hQ : r * K + 1 ≤ fieldSize r K := by
    unfold fieldSize ceilLog floorLog
    dsimp only
    split_ifs with h
    · exact h
    · exact (Nat.lt_pow_succ_log_self (by norm_num) _).le
  have hQ0 : 0 < fieldSize r K := by
    have : 1 ≤ r * K := Nat.mul_pos hr hK
    omega
  have hQ2 : 2 ≤ fieldSize r K := by
    have : 1 ≤ r * K := Nat.mul_pos hr hK
    omega
  have hrange : ∀ v, id v < fieldSize r K ^ K := fun v =>
    (range v).trans_le (Nat.pow_le_pow_left hQ2 K)
  have h1 : ∀ v, ∃ a : F, Separates G e K id v a := fun v =>
    exists_sep G e r K hK hQ degree id hid hrange v
  have h2 : ∀ v, Separates G e K id v (firstSeparating G e K id v) := fun v =>
    first_sep G e K id v (h1 v)
  refine ⟨h1, h2, ?_, ?_⟩
  · intro v
    have a1 := (e (firstSeparating G e K id v)).isLt
    have a2 := (e ((identifierPoly e K (id v)).eval (firstSeparating G e K id v))).isLt
    unfold polynomialColor
    simp only
    nlinarith
  · intro u v huv hc
    have a2 := (e ((identifierPoly e K (id u)).eval (firstSeparating G e K id u))).isLt
    have a3 := (e ((identifierPoly e K (id v)).eval (firstSeparating G e K id v))).isLt
    unfold polynomialColor at hc
    simp only at hc
    have hd := congrArg (· / fieldSize r K) hc
    have hm := congrArg (· % fieldSize r K) hc
    simp only [Nat.mul_add_div hQ0, Nat.div_eq_of_lt a2, Nat.div_eq_of_lt a3,
      Nat.mul_add_mod, Nat.mod_eq_of_lt a2, Nat.mod_eq_of_lt a3, add_zero] at hd hm
    have hA : firstSeparating G e K id u = firstSeparating G e K id v :=
      e.injective (Fin.ext hd)
    have hB := e.injective (Fin.ext hm)
    exact h2 u v huv (by rw [hB, hA])
end EditMulticoloring.Code
end

theorem solution : type_of% @EditMulticoloring.Code.chk_polynomial_coloring := @EditMulticoloring.Code.chk_polynomial_coloring
