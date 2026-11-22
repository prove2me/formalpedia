-- Prove2me | solution 1 for Castro2006.groups_order_pq
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T16:13:02.795811+00:00
-- url     : https://prove2.me/submissions/fc6cbeb2-8410-47a4-8449-b4266675869d

import Mathlib

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    {G : Type} [Group G] [Fintype G] (hcard : Fintype.card G = p * q) :
    IsCyclic G ∨ (q ∣ p - 1 ∧
      ∃ φ : Multiplicative (ZMod q) →* MulAut (Multiplicative (ZMod p)),
        φ ≠ 1 ∧ Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod p)) (Multiplicative (ZMod q)) φ)) := by
  have := Fact.mk hp
  have := Fact.mk hq
  have hG : Nat.card G = p * q := by rw [Nat.card_eq_fintype_card, hcard]
  have hpq : p ≠ q := hqp.ne'
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  -- A Sylow `p`-subgroup `P` has order `p`.
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hP : Nat.card P = p := by
    rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hp.ne_zero hq.ne_zero,
      Finsupp.add_apply, hp.factorization, hq.factorization]
    simp [hpq.symm]
  have hPidx : (P : Subgroup G).index = q := by
    have h := (P : Subgroup G).card_mul_index
    rw [hP, hG] at h
    exact (Nat.eq_of_mul_eq_mul_left hp.pos h)
  -- The number of Sylow `p`-subgroups divides `q` and is `≡ 1 mod p`, hence is `1`.
  have hnum : Nat.card (Sylow p G) = 1 := by
    have h1 := card_sylow_modEq_one p G
    have h2 := P.card_dvd_index
    rw [hPidx] at h2
    rcases (Nat.dvd_prime hq).1 h2 with h | h
    · exact h
    · exfalso
      rw [h, Nat.ModEq, Nat.mod_eq_of_lt hqp, Nat.mod_eq_of_lt hp.one_lt] at h1
      exact hq.one_lt.ne' h1
  have : Subsingleton (Sylow p G) := by
    have := (Nat.card_eq_one_iff_unique.1 hnum).1
    exact this
  have hPn : (P : Subgroup G).Normal := P.normal_of_subsingleton
  -- A subgroup `Q` of order `q` (Cauchy).
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) q (by rw [hG]; exact dvd_mul_left q p)
  set Q : Subgroup G := Subgroup.zpowers g
  have hQ : Nat.card Q = q := by rw [Nat.card_zpowers, hg]
  -- `Q` is a complement of the normal subgroup `P`, so `G ≅ P ⋊ Q`.
  have hc : (P : Subgroup G).IsComplement' Q :=
    Subgroup.isComplement'_of_coprime (by rw [hP, hQ, hG]) (by rw [hP, hQ]; exact hcop)
  have hcardp : Nat.card (Multiplicative (ZMod p)) = p := by simp
  have hcardq : Nat.card (Multiplicative (ZMod q)) = q := by simp
  have : IsCyclic P := isCyclic_of_prime_card hP
  have : IsCyclic Q := isCyclic_of_prime_card hQ
  let eP : P ≃* Multiplicative (ZMod p) := mulEquivOfCyclicCardEq (hP.trans hcardp.symm)
  let eQ : Q ≃* Multiplicative (ZMod q) := mulEquivOfCyclicCardEq (hQ.trans hcardq.symm)
  obtain ⟨φ, ⟨e⟩⟩ : ∃ φ : Multiplicative (ZMod q) →* MulAut (Multiplicative (ZMod p)),
      Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod p)) (Multiplicative (ZMod q)) φ) :=
    ⟨_, ⟨(SemidirectProduct.mulEquivSubgroup hc).symm.trans (SemidirectProduct.congr' eP eQ)⟩⟩
  by_cases h1 : φ = 1
  · -- Trivial action: `G ≅ ℤ_p × ℤ_q`, which is cyclic.
    left
    subst h1
    have hcyc : IsCyclic (Multiplicative (ZMod p) × Multiplicative (ZMod q)) :=
      Group.isCyclic_prod_iff.2 ⟨inferInstance, inferInstance, by rw [hcardp, hcardq]; exact hcop⟩
    exact (e.trans SemidirectProduct.mulEquivProd).isCyclic.2 hcyc
  · -- Nontrivial action: some `φ x` has order `q`, which divides `|Aut ℤ_p| = p - 1`.
    right
    refine ⟨?_, φ, h1, ⟨e⟩⟩
    obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact h1 (MonoidHom.ext hcon)
    have hdvd : orderOf (φ x) ∣ q :=
      (orderOf_map_dvd φ x).trans ((orderOf_dvd_natCard x).trans hcardq.dvd)
    have hord : orderOf (φ x) = q := by
      rcases (Nat.dvd_prime hq).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hx
      · exact h
    have := orderOf_dvd_natCard (φ x)
    rwa [hord, IsCyclic.card_mulAut, hcardp, Nat.totient_prime hp] at this
