-- Prove2me | solution 1 for DetDLP.primitive_root_from_generating_set
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:50:11.76149+00:00
-- url     : https://prove2.me/submissions/dead4a7e-0c05-4870-a95f-610dde4c31bf

import Mathlib

set_option autoImplicit false

private lemma orderOf_prod_of_pairwise_coprime {G : Type*} [CommGroup G]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → G)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (orderOf (f i)) (orderOf (f j))) :
    orderOf (∏ i ∈ s, f i) = ∏ i ∈ s, orderOf (f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop_s : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (orderOf (f i)) (orderOf (f j)) :=
      fun i hi j hj hij => hcop i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have ihs := ih hcop_s
    have hcop_a : Nat.Coprime (orderOf (f a)) (orderOf (∏ i ∈ s, f i)) := by
      rw [ihs]
      exact Nat.Coprime.prod_right fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.all _ _) hcop_a, ihs]

theorem solution :
    ∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
      (∀ X : (ZMod p)ˣ, ∃ A B : Fin m → (ZMod p)ˣ,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∏ i : Fin m, (A i * B i)) = X) →
      (∀ π ∈ (p - 1).primeFactors,
        ∃ i : Fin m, ∃ a ∈ F i, a ^ ((p - 1) / π) ≠ 1) ∧
      (∀ a : ℕ → (ZMod p)ˣ,
        (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) →
        orderOf (∏ π ∈ (p - 1).primeFactors,
          (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)) = p - 1) := by
  intro p m _ F hcover
  have hp : p.Prime := Fact.out
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hpm1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpm1_ne : p - 1 ≠ 0 := ne_of_gt hpm1_pos
  constructor
  · -- Part 1: Every prime π ∣ (p - 1) has a witness a ∈ F i with a^((p - 1)/π) ≠ 1
    intro π hπ
    have hπ_prime : π.Prime := Nat.prime_of_mem_primeFactors hπ
    have hπ_dvd : π ∣ p - 1 := Nat.dvd_of_mem_primeFactors hπ
    by_contra hno
    push Not at hno
    -- Every element of every F i has ((p - 1)/π)-th power equal to 1, hence so does every X
    have hall : ∀ X : (ZMod p)ˣ, X ^ ((p - 1) / π) = 1 := by
      intro X
      obtain ⟨A, B, hAB, rfl⟩ := hcover X
      rw [← Finset.prod_pow]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [mul_pow, hno i (A i) (hAB i).1, hno i (B i) (hAB i).2, one_mul]
    -- But (ZMod p)ˣ is cyclic, so there exists a generator g of order p - 1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord_g : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
    have hdvd : orderOf g ∣ (p - 1) / π := orderOf_dvd_iff_pow_eq_one.mpr (hall g)
    rw [hord_g] at hdvd
    have hlt : (p - 1) / π < p - 1 := Nat.div_lt_self hpm1_pos hπ_prime.one_lt
    have hpos_div : 0 < (p - 1) / π :=
      Nat.div_pos (Nat.le_of_dvd hpm1_pos hπ_dvd) hπ_prime.pos
    exact absurd (Nat.le_of_dvd hpos_div hdvd) (not_le.mpr hlt)
  · -- Part 2: Exact order of the product h = ∏ π, (a π)^((p - 1) / π^{e_π})
    intro a ha
    let e : ℕ → ℕ := fun π => (p - 1).factorization π
    let hfun : ℕ → (ZMod p)ˣ := fun π => (a π) ^ ((p - 1) / π ^ e π)
    have hord_each : ∀ π ∈ (p - 1).primeFactors, orderOf (hfun π) = π ^ e π := by
      intro π hπ
      have hπ_prime : π.Prime := Nat.prime_of_mem_primeFactors hπ
      have hpe_dvd : π ^ e π ∣ p - 1 := Nat.ordProj_dvd (p - 1) π
      have he_pos : 0 < e π := Nat.pos_of_ne_zero ((Finsupp.mem_support_iff).mp hπ)
      have hpow_one : (hfun π) ^ (π ^ e π) = 1 := by
        dsimp only [hfun]
        rw [← pow_mul, Nat.div_mul_cancel hpe_dvd, ← hcard, pow_card_eq_one]
      have hdvd : orderOf (hfun π) ∣ π ^ e π := orderOf_dvd_iff_pow_eq_one.mpr hpow_one
      obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow hπ_prime).mp hdvd
      by_cases hke : k = e π
      · rw [hk_eq, hke]
      · exfalso
        have hk_lt : k ≤ e π - 1 := by omega
        have hpow_prev : (hfun π) ^ (π ^ (e π - 1)) = 1 := by
          rw [← orderOf_dvd_iff_pow_eq_one, hk_eq]
          exact Nat.pow_dvd_pow π hk_lt
        have hexp_eq : ((p - 1) / π ^ e π) * π ^ (e π - 1) = (p - 1) / π := by
          have hπ_pos : 0 < π := hπ_prime.pos
          have hpe_eq : π ^ e π = π ^ (e π - 1) * π := by
            rw [← pow_succ, Nat.sub_add_cancel he_pos]
          have hmul : ((p - 1) / π ^ e π) * π ^ (e π - 1) * π = p - 1 := by
            rw [mul_assoc, ← hpe_eq, Nat.div_mul_cancel hpe_dvd]
          have hdiv := congrArg (· / π) hmul
          simpa [Nat.mul_div_cancel _ hπ_pos] using hdiv
        dsimp only [hfun] at hpow_prev
        rw [← pow_mul, hexp_eq] at hpow_prev
        exact ha π hπ hpow_prev
    have hcop : ∀ π₁ ∈ (p - 1).primeFactors, ∀ π₂ ∈ (p - 1).primeFactors,
        π₁ ≠ π₂ → Nat.Coprime (orderOf (hfun π₁)) (orderOf (hfun π₂)) := by
      intro π₁ h₁ π₂ h₂ hne
      rw [hord_each π₁ h₁, hord_each π₂ h₂]
      exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors h₁)
        (Nat.prime_of_mem_primeFactors h₂)).mpr hne).pow _ _
    rw [orderOf_prod_of_pairwise_coprime _ hfun hcop]
    rw [Finset.prod_congr rfl hord_each]
    exact Nat.prod_factorization_pow_eq_self hpm1_ne
