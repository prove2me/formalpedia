-- Prove2me | solution 1 for Erdos287.cancel_ordered_prime_layers_with_reserve_cofactors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:13:24.549009+00:00
-- url     : https://prove2.me/submissions/dda40f63-fa44-4a17-ab47-4fa971df59e7

import Mathlib
import Theorems.Thm_Erdos287_cancel_all_prime_layers_with_reserve_cofactors

open Finset

set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem den_dvd_of_int_div (A : ℤ) (L : ℕ) :
    ((A : ℚ) / L).den ∣ L := by
  have h : (A : ℚ) / L = Rat.divInt A (L : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast]
  rw [h]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)

private theorem has_common_denominator (x : ℚ) (Q : ℕ) (hQ : 0 < Q)
    (hx : x.den ∣ Q) : ∃ A : ℤ, x = (A : ℚ) / Q := by
  obtain ⟨k, hk⟩ := hx
  refine ⟨x.num * k, ?_⟩
  have hkN : k ≠ 0 := by
    rintro rfl
    simp at hk
    omega
  have hkpos : (0 : ℚ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero hkN
  have hd : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_ne_zero
  calc
    x = (x.num : ℚ) / x.den := x.num_div_den.symm
    _ = ((x.num * k : ℤ) : ℚ) / Q := by
      rw [hk]
      push_cast
      field_simp

private theorem prime_free_add (p : ℕ) (hp : p.Prime) (x y : ℚ)
    (hx : ¬ p ∣ x.den) (hy : ¬ p ∣ y.den) : ¬ p ∣ (x + y).den := by
  intro h
  exact (hp.dvd_mul.mp (h.trans (Rat.add_den_dvd x y))).elim hx hy

private theorem prime_free_finset_sum {α : Type*} (s : Finset α) (f : α → ℚ)
    {p : ℕ} (hp : p.Prime) (h : ∀ a ∈ s, ¬ p ∣ (f a).den) :
    ¬ p ∣ (∑ a ∈ s, f a).den := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hp.not_dvd_one
  | insert a s ha ih =>
      rw [sum_insert ha]
      exact prime_free_add p hp _ _ (h a (mem_insert_self a s))
        (ih (fun b hb => h b (mem_insert_of_mem hb)))

private theorem prime_free_list_sum {α : Type*} (l : List α) (f : α → ℚ)
    {p : ℕ} (hp : p.Prime) (h : ∀ a ∈ l, ¬ p ∣ (f a).den) :
    ¬ p ∣ ((l.map f).sum).den := by
  induction l with
  | nil => simpa using hp.not_dvd_one
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons]
      exact prime_free_add p hp _ _ (h a (List.mem_cons.mpr (Or.inl rfl)))
        (ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb))))

/-- Correct an ordered list of primes using reserves that preserve the
integrality already obtained at each earlier prime. -/
theorem solution (ps : List ℕ) (Q : ℕ) (x : ℚ) (E L : ℕ → ℕ)
    (S : ℕ → ℕ → Finset ℕ) (hQ : 0 < Q) (hx : x.den ∣ Q)
    (hprime : ∀ p ∈ ps, p.Prime)
    (hsplit : ∀ p ∈ ps, p ^ E p * L p = Q ∧ ¬ p ∣ L p)
    (hcard : ∀ p ∈ ps, ∀ a ∈ Finset.Icc 1 (E p), p - 1 ≤ (S p a).card)
    (hcof : ∀ p ∈ ps, ∀ a ∈ Finset.Icc 1 (E p), ∀ c ∈ S p a, 0 < c ∧ c ∣ L p)
    (hcross : ps.Pairwise (fun p q => p ≠ q ∧
      ∀ a ∈ Finset.Icc 1 (E q), ∀ c ∈ S q a, ¬ p ∣ q ^ a * c)) :
    ∃ T : ℕ → ℕ → Finset ℕ,
      (∀ p ∈ ps, ∀ a, T p a ⊆ S p a ∧ (T p a).card ≤ p - 1) ∧
      ∀ p ∈ ps, ¬ p ∣ (x + (ps.map (fun q =>
        ∑ a ∈ Finset.Icc 1 (E q), ∑ c ∈ T q a, (1 : ℚ) / ((q : ℚ) ^ a * c))).sum).den := by
  induction ps generalizing x with
  | nil => exact ⟨fun _ _ => ∅, by simp, by simp⟩
  | cons p ps ih =>
      have hhead : p ∈ p :: ps := List.mem_cons.mpr (Or.inl rfl)
      have htail {q : ℕ} (hq : q ∈ ps) : q ∈ p :: ps := List.mem_cons.mpr (Or.inr hq)
      obtain ⟨A, hA⟩ := has_common_denominator x Q hQ hx
      have hscale : (p : ℚ) ^ E p * L p = Q := by exact_mod_cast (hsplit p hhead).1
      have hA' : x = (A : ℚ) / ((p : ℚ) ^ E p * L p) := by rw [hscale, hA]
      obtain ⟨U, hU, K, hK⟩ :=
        Erdos287.cancel_all_prime_layers_with_reserve_cofactors p (E p) (L p) A (S p)
          (hprime p hhead) (hsplit p hhead).2 (hcard p hhead) (hcof p hhead)
      let headMass := ∑ a ∈ Icc 1 (E p), ∑ c ∈ U a, (1 : ℚ) / ((p : ℚ) ^ a * c)
      have hheadMass : x + headMass = (K : ℚ) / L p := by rw [hA']; exact hK
      have hden : (x + headMass).den ∣ L p := by rw [hheadMass]; exact den_dvd_of_int_div _ _
      have hdiv : L p ∣ Q := (hsplit p hhead).1 ▸ dvd_mul_left (L p) (p ^ E p)
      obtain ⟨T, hT, hfinal⟩ := ih (x + headMass) (hden.trans hdiv)
        (fun q hq => hprime q (htail hq)) (fun q hq => hsplit q (htail hq))
        (fun q hq => hcard q (htail hq)) (fun q hq => hcof q (htail hq))
        (List.pairwise_cons.mp hcross).2
      let R (q : ℕ) := if q = p then U else T q
      have htNe (q : ℕ) (hq : q ∈ ps) : q ≠ p :=
        ((List.pairwise_cons.mp hcross).1 q hq).1.symm
      refine ⟨R, ?_, ?_⟩
      · intro q hq a
        rcases List.mem_cons.mp hq with rfl | hq
        · simpa [R] using hU a
        · simpa [R, htNe q hq] using hT q hq a
      let mass (q : ℕ) := ∑ a ∈ Icc 1 (E q), ∑ c ∈ T q a, (1 : ℚ) / ((q : ℚ) ^ a * c)
      have hmap : (ps.map (fun q => ∑ a ∈ Icc 1 (E q), ∑ c ∈ R q a,
          (1 : ℚ) / ((q : ℚ) ^ a * c))) = ps.map mass := by
        apply List.map_congr_left
        intro q hq
        simp [R, mass, htNe q hq]
      have hmass : (p :: ps).map (fun q => ∑ a ∈ Icc 1 (E q), ∑ c ∈ R q a,
          (1 : ℚ) / ((q : ℚ) ^ a * c)) = headMass :: ps.map mass := by
        rw [List.map_cons, hmap]
        simp [R, headMass]
      intro q hq
      rw [hmass, List.sum_cons, ← add_assoc]
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        apply prime_free_add p (hprime p hhead) _ _ (fun hd => (hsplit p hhead).2 (hd.trans hden))
        apply prime_free_list_sum _ _ (hprime p hhead)
        intro q hq
        apply prime_free_finset_sum _ _ (hprime p hhead)
        intro a ha
        apply prime_free_finset_sum _ _ (hprime p hhead)
        intro c hc
        have hcast : (q : ℚ) ^ a * c = ((q ^ a * c : ℕ) : ℚ) := by rw [Nat.cast_mul, Nat.cast_pow]
        rw [hcast]
        exact fun hd => ((List.pairwise_cons.mp hcross).1 q hq).2 a ha c ((hT q hq a).1 hc)
          (hd.trans (den_dvd_of_int_div 1 (q ^ a * c)))
      · exact hfinal q hq

