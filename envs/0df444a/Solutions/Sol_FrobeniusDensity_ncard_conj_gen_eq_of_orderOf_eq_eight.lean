-- Prove2me | solution 1 for FrobeniusDensity.ncard_conj_gen_eq_of_orderOf_eq_eight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/967fe2f6-28b4-5c19-a9fc-b4c0161c3b0c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight

set_option autoImplicit false

open scoped Classical

namespace FltWs24
namespace RationalClass

variable {G : Type*} [Group G]

theorem coprime_mod_iff {k n : ℕ} : (k % n).Coprime n ↔ k.Coprime n := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

theorem card_filter_conj_eq [Fintype G] (a b : G) (h : IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card
      = Fintype.card (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have key : ∀ g : G, g * a * g⁻¹ = b ↔ c⁻¹ * g ∈ Subgroup.centralizer ({a} : Set G) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      have h1 : g * a * g⁻¹ = c * a * c⁻¹ := by rw [hg, hc]
      have h2 : c⁻¹ * (g * a * g⁻¹) * c = a := by
        rw [h1]; group
      calc c⁻¹ * g * a = c⁻¹ * (g * a * g⁻¹) * c * (c⁻¹ * g) := by group
        _ = a * (c⁻¹ * g) := by rw [h2]
    · intro hg
      have h3 : g * a * g⁻¹ = c * (c⁻¹ * g * a) * g⁻¹ := by group
      rw [h3, hg, ← hc]; group
  rw [← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.mulLeft c⁻¹) (fun g => ?_))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulLeft]
  exact key g

theorem card_filter_conj_eq_zero [Fintype G] (a b : G) (h : ¬ IsConj a b) :
    (Finset.univ.filter (fun g : G => g * a * g⁻¹ = b)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro g _ hg
  exact h (isConj_iff.mpr ⟨g, hg⟩)

theorem centralizer_pow_eq_of_coprime (σ : G) {k : ℕ} (hk : k.Coprime (orderOf σ)) :
    Subgroup.centralizer ({σ ^ k} : Set G) = Subgroup.centralizer ({σ} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hk
    rw [← hm]
    exact (Commute.pow_right (show Commute g (σ ^ k) from h) m)
  · intro h
    exact (Commute.pow_right (show Commute g σ from h) k)

theorem ncard_conj_gen_eq_of_rational [Finite G] (σ τ : G)
    (hrat : ∀ k : ℕ, k.Coprime (orderOf σ) → IsConj σ (σ ^ k)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = if IsConj σ τ then (orderOf σ).totient * Nat.card (Subgroup.centralizer ({σ} : Set G))
        else 0 := by
  haveI := Fintype.ofFinite G
  set n := orderOf σ with hn
  have hn0 : 0 < n := orderOf_pos σ
  set K : Finset ℕ := (Finset.range n).filter (fun k => n.Coprime k) with hK
  have hKcard : K.card = n.totient := (Nat.totient_eq_card_coprime n).symm
  set S : Set G := {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ} with hS
  set T : ℕ → Finset G := fun k => Finset.univ.filter (fun g : G => g * σ ^ k * g⁻¹ = τ) with hT
  have hST : S.toFinset = K.biUnion T := by
    ext g
    simp only [Set.mem_toFinset, hS, Set.mem_setOf_eq, Finset.mem_biUnion, hK, hT,
      Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, hgk⟩
      refine ⟨k % n, ⟨Nat.mod_lt _ hn0, ?_⟩, ?_⟩
      · exact Nat.coprime_comm.mp (coprime_mod_iff.mpr hk)
      · rwa [pow_mod_orderOf]
    · rintro ⟨k, ⟨-, hk⟩, hgk⟩
      exact ⟨k, Nat.coprime_comm.mp hk, hgk⟩
  have hdisj : (K : Set ℕ).PairwiseDisjoint T := by
    intro k hk k' hk' hne
    simp only [Finset.coe_filter, hK, Set.mem_setOf_eq, Finset.mem_range] at hk hk'
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
    apply hne
    have hpow : σ ^ k = σ ^ k' := by
      have := hg.trans hg'.symm
      simpa using this
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hk.1) (Set.mem_Iio.mpr hk'.1) hpow
  rw [Set.ncard_eq_toFinset_card' S, hST, Finset.card_biUnion hdisj]
  by_cases hc : IsConj σ τ
  · rw [if_pos hc]
    have hterm : ∀ k ∈ K, (T k).card = Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
      intro k hk
      simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
      have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
      have hconj : IsConj (σ ^ k) τ := (hrat k hk').symm.trans hc
      rw [hT, card_filter_conj_eq _ _ hconj, centralizer_pow_eq_of_coprime σ hk',
        Nat.card_eq_fintype_card]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hKcard]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun k hk => ?_
    simp only [hK, Finset.mem_filter, Finset.mem_range] at hk
    have hk' : k.Coprime (orderOf σ) := Nat.coprime_comm.mp hk.2
    have hnc : ¬ IsConj (σ ^ k) τ := fun h => hc ((hrat k hk').trans h)
    exact card_filter_conj_eq_zero _ _ hnc

theorem ncard_conj_gen_eq_of_orderOf_eq_eight [Finite G] (σ τ : G)
    (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = 2 * Nat.card (Subgroup.centralizer ({σ} : Set G)) *
          ((if IsConj σ τ then 1 else 0) + (if IsConj (σ ^ 5) τ then 1 else 0)) := by
  haveI := Fintype.ofFinite G
  set n := orderOf σ with hn
  have hn0 : 0 < n := orderOf_pos σ
  set K : Finset ℕ := (Finset.range n).filter (fun k => n.Coprime k) with hK
  set S : Set G := {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ} with hS
  set T : ℕ → Finset G := fun k => Finset.univ.filter (fun g : G => g * σ ^ k * g⁻¹ = τ) with hT
  have hST : S.toFinset = K.biUnion T := by
    ext g
    simp only [Set.mem_toFinset, hS, Set.mem_setOf_eq, Finset.mem_biUnion, hK, hT,
      Finset.mem_filter, Finset.mem_range, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨k, hk, hgk⟩
      refine ⟨k % n, ⟨Nat.mod_lt _ hn0, ?_⟩, ?_⟩
      · exact Nat.coprime_comm.mp (coprime_mod_iff.mpr hk)
      · rwa [pow_mod_orderOf]
    · rintro ⟨k, ⟨-, hk⟩, hgk⟩
      exact ⟨k, Nat.coprime_comm.mp hk, hgk⟩
  have hdisj : (K : Set ℕ).PairwiseDisjoint T := by
    intro k hk k' hk' hne
    simp only [Finset.coe_filter, hK, Set.mem_setOf_eq, Finset.mem_range] at hk hk'
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hg hg'
    apply hne
    have hpow : σ ^ k = σ ^ k' := by
      have := hg.trans hg'.symm
      simpa using this
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hk.1) (Set.mem_Iio.mpr hk'.1) hpow
  rw [Set.ncard_eq_toFinset_card' S, hST, Finset.card_biUnion hdisj]

  have hK' : K = {1, 3, 5, 7} := by rw [hK, h8]; decide

  have hcop : ∀ k ∈ ({1, 3, 5, 7} : Finset ℕ), k.Coprime (orderOf σ) := by
    intro k hk; rw [← hn, h8]; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  have hcard : ∀ (k : ℕ), k.Coprime (orderOf σ) → ∀ (x : G), IsConj (σ ^ k) x →
      (T k).card = (if IsConj x τ then Nat.card (Subgroup.centralizer ({σ} : Set G)) else 0) := by
    intro k hk x hx
    by_cases hc : IsConj x τ
    · rw [if_pos hc, hT, card_filter_conj_eq _ _ (hx.trans hc), centralizer_pow_eq_of_coprime σ hk,
        Nat.card_eq_fintype_card]
    · rw [if_neg hc]
      exact card_filter_conj_eq_zero _ _ (fun h => hc (hx.symm.trans h))

  have h7 : IsConj (σ ^ 7) (σ ^ 5) := by
    obtain ⟨c, hc⟩ := isConj_iff.mp h3
    refine (isConj_iff.mpr ⟨c, ?_⟩).symm
    have : c * σ ^ 5 * c⁻¹ = (c * σ * c⁻¹) ^ 5 := by
      simp [conj_pow]
    rw [this, hc, ← pow_mul]
    rw [show 3 * 5 = 8 + 7 by norm_num, pow_add, ← h8, hn, pow_orderOf_eq_one, one_mul]
  rw [hK', Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton,
    hcard 1 (hcop 1 (by simp)) σ (by rw [pow_one]),
    hcard 3 (hcop 3 (by simp)) σ h3.symm,
    hcard 5 (hcop 5 (by simp)) (σ ^ 5) (IsConj.refl _),
    hcard 7 (hcop 7 (by simp)) (σ ^ 5) h7]
  split_ifs <;> ring

end FltWs24.RationalClass

open scoped Classical in
theorem solution {G : Type*} [Group G] [Finite G]
    (σ τ : G) (h8 : orderOf σ = 8) (h3 : IsConj σ (σ ^ 3)) :
    {g : G | ∃ k : ℕ, k.Coprime (orderOf σ) ∧ g * σ ^ k * g⁻¹ = τ}.ncard
      = 2 * Nat.card (Subgroup.centralizer ({σ} : Set G)) *
          ((if IsConj σ τ then 1 else 0) + (if IsConj (σ ^ 5) τ then 1 else 0)) :=
  FltWs24.RationalClass.ncard_conj_gen_eq_of_orderOf_eq_eight σ τ h8 h3

end S_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight
end P2MW
export P2MW.S_FrobeniusDensity_ncard_conj_gen_eq_of_orderOf_eq_eight (solution)
