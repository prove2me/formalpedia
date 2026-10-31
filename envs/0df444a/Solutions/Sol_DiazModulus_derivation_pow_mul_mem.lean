-- Prove2me | solution 1 for DiazModulus.derivation_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:03:45.139982+00:00
-- url     : https://prove2.me/submissions/744febcb-632c-4f5f-a09e-eb38f15993e1

import Mathlib

open Complex ComplexConjugate

/-! # DALAG Lemma 8.16: derivatives of `P·Q^α` modulo `J`
Write `D^ks` for the composite of the derivations `D_k` along the list `ks` and
`Q^α = Π_j Q_j^{α_j}`. We prove, for all `P` and `α` at once, by induction on `ks` peeling off the
derivation applied first (the last entry of the list), that `D^ks(P·Q^α)` is congruent modulo `J`
to `[count ks = α]·α!·P` whenever `|ks| ≤ |α|`. Empty list: `P·Q^α ∈ J` as soon as some `α_j > 0`.
Step `ks = l ++ [k]`: Leibniz gives `D_k(P·Q^α) = D_kP·Q^α + Σ_j α_j·D_k(Q_j)·P·Q^{α−e_j}`. The first
term contributes `0`, since `count l = α` would force `|l| = |α|`. The `j`-th term is
`[count l = α−e_j]·(α−e_j)!·α_j·D_kQ_j·P` by induction (with `P` replaced by `α_j·D_kQ_j·P`),
and `D_kQ_j ≡ δ_kj` kills every `j ≠ k`. For `j = k`: if `α_k = 0` both sides vanish; otherwise
`count (l ++ [k]) = α ↔ count l = α − e_k` and `α! = α_k·(α − e_k)!`. No commutation of the
derivations is used; the congruences are computed in `S ⧸ J`. -/

namespace C13_W3
open Finset

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem deriv_prod (D : Derivation R S S) (f : Fin n → S) (s : Finset (Fin n)) :
    D (∏ j ∈ s, f j) = ∑ j ∈ s, (∏ i ∈ s.erase j, f i) * D (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, erase_insert ha, smul_eq_mul,
      smul_eq_mul, mul_sum]
    have h : ∀ j ∈ s, (∏ i ∈ (insert a s).erase j, f i) * D (f j) =
        f a * ((∏ i ∈ s.erase j, f i) * D (f j)) := by
      intro j hj
      have hne : a ≠ j := by rintro rfl; exact ha hj
      rw [erase_insert_of_ne hne, prod_insert (fun h => ha (mem_of_mem_erase h)), mul_assoc]
    rw [sum_congr rfl h]
    ring

/-- `Q^β = Π_i Q_i^{β_i}`. -/
def Qp (Q : Fin n → S) (β : Fin n → ℕ) : S := ∏ i, Q i ^ β i

theorem Qp_update (Q : Fin n → S) (α : Fin n → ℕ) (j : Fin n) (b : ℕ) :
    Qp Q (Function.update α j b) = Q j ^ b * ∏ i ∈ univ.erase j, Q i ^ α i := by
  unfold Qp
  rw [← mul_prod_erase univ (fun i => Q i ^ Function.update α j b i) (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

theorem deriv_Qp (D : Derivation R S S) (Q : Fin n → S) (α : Fin n → ℕ) :
    D (Qp Q α) = ∑ j, (α j : S) * D (Q j) * Qp Q (Function.update α j (α j - 1)) := by
  change D (∏ i, Q i ^ α i) = _
  rw [deriv_prod]
  apply sum_congr rfl
  intro j _
  rw [Qp_update, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem sum_count (l : List (Fin n)) : ∑ i, l.count i = l.length := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.count_cons, sum_add_distrib, ih]

theorem count_append_singleton (l : List (Fin n)) (k i : Fin n) :
    (l ++ [k]).count i = l.count i + if i = k then 1 else 0 := by
  rw [List.count_append]
  congr 1
  by_cases h : i = k
  · subst h; simp
  · have h' : ¬k = i := fun e => h e.symm
    simp [h, h']

/-- `D^ks`, the composite along the list `ks` (first entry outermost). -/
def Dl (D : Fin n → Derivation R S S) (ks : List (Fin n)) : Module.End R S :=
  (ks.map fun i => (D i).toLinearMap).prod

theorem main (D : Fin n → Derivation R S S) (J : Ideal S) (Q : Fin n → S) (hQ : ∀ j, Q j ∈ J)
    (hDQ : ∀ i j, D i (Q j) - (if i = j then 1 else 0) ∈ J) :
    ∀ (ks : List (Fin n)) (P : S) (α : Fin n → ℕ), ks.length ≤ ∑ i, α i →
      Ideal.Quotient.mk J (Dl D ks (P * Qp Q α)) =
        Ideal.Quotient.mk J (if (fun i => ks.count i) = α then
          ((∏ i, (α i).factorial : ℕ) : S) * P else 0) := by
  intro ks
  induction ks using List.reverseRecOn with
  | nil =>
    intro P α _
    have hDl : Dl D [] (P * Qp Q α) = P * Qp Q α := by simp [Dl]
    rw [hDl]
    by_cases h0 : (fun i => ([] : List (Fin n)).count i) = α
    · rw [if_pos h0]
      have hα : α = fun _ => 0 := by rw [← h0]; funext i; simp
      subst hα
      simp [Qp]
    · rw [if_neg h0, map_zero, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨j, hj⟩ : ∃ j, α j ≠ 0 := by
        by_contra hc
        push Not at hc
        exact h0 (funext fun j => by simp [hc j])
      apply J.mul_mem_left
      unfold Qp
      rw [← mul_prod_erase univ (fun i => Q i ^ α i) (mem_univ j)]
      exact J.mul_mem_right _ (J.pow_mem_of_mem (hQ j) _ (Nat.pos_of_ne_zero hj))
  | append_singleton l k ih =>
    intro P α hlen
    rw [List.length_append, List.length_singleton] at hlen
    have hDl : Dl D (l ++ [k]) (P * Qp Q α) = Dl D l (D k (P * Qp Q α)) := by
      simp [Dl, List.map_append, List.prod_append, Module.End.mul_apply]
    have hexp : D k (P * Qp Q α) = D k P * Qp Q α +
        ∑ j, ((α j : S) * D k (Q j) * P) * Qp Q (Function.update α j (α j - 1)) := by
      rw [Derivation.leibniz, deriv_Qp, smul_eq_mul, smul_eq_mul, mul_sum, add_comm]
      congr 1
      · ring
      · apply sum_congr rfl
        intro j _
        ring
    rw [hDl, hexp, map_add, map_sum, map_add, map_sum]
    have hcnt : ∀ (m : List (Fin n)) (β : Fin n → ℕ), (fun i => m.count i) = β →
        ∑ i, β i = m.length := by
      rintro m β rfl
      exact sum_count m
    have h1 : Ideal.Quotient.mk J (Dl D l (D k P * Qp Q α)) = 0 := by
      rw [ih _ _ (by omega), if_neg, map_zero]
      intro h
      have := hcnt _ _ h
      omega
    rw [h1, zero_add]
    have hβsum : ∀ j, ∑ i, α i ≤ ∑ i, Function.update α j (α j - 1) i + 1 := by
      intro j
      rw [← add_sum_erase univ (Function.update α j (α j - 1)) (mem_univ j),
        ← add_sum_erase univ α (mem_univ j), Function.update_self,
        sum_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_erase hi) _ α)]
      have e : ∑ x ∈ univ.erase j, α x = (univ.erase j).sum α := rfl
      omega
    have hterm : ∀ j, Ideal.Quotient.mk J (Dl D l (((α j : S) * D k (Q j) * P) *
        Qp Q (Function.update α j (α j - 1)))) =
        if k = j then Ideal.Quotient.mk J (if (fun i => l.count i) = Function.update α j (α j - 1)
          then ((∏ i, (Function.update α j (α j - 1) i).factorial : ℕ) : S) * ((α j : S) * P)
          else 0) else 0 := by
      intro j
      rw [ih _ _ (by have := hβsum j; omega)]
      have hD : Ideal.Quotient.mk J (D k (Q j)) = Ideal.Quotient.mk J (if k = j then 1 else 0) :=
        Ideal.Quotient.eq.mpr (hDQ k j)
      by_cases hc : (fun i => l.count i) = Function.update α j (α j - 1)
      · rw [if_pos hc]
        by_cases hkj : k = j
        · rw [if_pos hkj, if_pos hc]
          simp only [map_mul, hD, if_pos hkj, map_one, mul_one]
        · rw [if_neg hkj]
          simp only [map_mul, hD, if_neg hkj, map_zero, mul_zero, zero_mul]
      · rw [if_neg hc, map_zero]
        split_ifs <;> simp
    rw [sum_congr rfl (fun j _ => hterm j), sum_ite_eq univ k, if_pos (mem_univ k)]
    by_cases hk : α k = 0
    · rw [if_neg (show ¬((fun i => (l ++ [k]).count i) = α) from ?_)]
      · split_ifs <;> simp [hk]
      · intro h
        have := congrFun h k
        simp only [count_append_singleton, ite_true] at this
        omega
    have hiff : ((fun i => l.count i) = Function.update α k (α k - 1)) ↔
        ((fun i => (l ++ [k]).count i) = α) := by
      constructor
      · intro h
        funext i
        have := congrFun h i
        rw [count_append_singleton]
        by_cases hi : i = k
        · subst hi
          simp at this ⊢
          omega
        · simp only [Function.update_of_ne hi, if_neg hi] at this ⊢
          omega
      · intro h
        funext i
        have := congrFun h i
        rw [count_append_singleton] at this
        by_cases hi : i = k
        · subst hi
          simp at this ⊢
          omega
        · simp only [Function.update_of_ne hi, if_neg hi] at this ⊢
          omega
    have hf : (∏ i, (α i).factorial) = α k * ∏ i, (Function.update α k (α k - 1) i).factorial := by
      rw [← mul_prod_erase univ (fun i => (α i).factorial) (mem_univ k),
        ← mul_prod_erase univ (fun i => (Function.update α k (α k - 1) i).factorial) (mem_univ k)]
      simp only [Function.update_self]
      rw [← mul_assoc, Nat.mul_factorial_pred hk]
      congr 1
      apply prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (ne_of_mem_erase hi)]
    by_cases hc : (fun i => l.count i) = Function.update α k (α k - 1)
    · rw [if_pos hc, if_pos (hiff.mp hc), hf]
      congr 1
      push_cast
      ring
    · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

end C13_W3

open C13_W3 in
theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ} (D : Fin n → Derivation R S S)
    (J : Ideal S) (Q : Fin n → S) (hQ : ∀ j, Q j ∈ J) (hDQ : ∀ i j, D i (Q j) - (if i = j then 1 else 0) ∈ J)
    (P : S) (α : Fin n → ℕ) (ks : List (Fin n)) (hks : ks.length ≤ ∑ i, α i) :
    (ks.map fun i => (D i).toLinearMap).prod (P * ∏ j, Q j ^ α j)
      - (if (fun i => ks.count i) = α then ((∏ i, (α i).factorial : ℕ) : S) * P else 0) ∈ J := by
  exact Ideal.Quotient.eq.mp (main D J Q hQ hDQ ks P α hks)
