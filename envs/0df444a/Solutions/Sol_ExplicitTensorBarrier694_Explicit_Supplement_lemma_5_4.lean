-- Prove2me | solution 1 for ExplicitTensorBarrier694.Explicit.Supplement.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:39:12.501809+00:00
-- url     : https://prove2.me/submissions/c14cfe25-41b3-4708-8d7e-e895fbf48678

import Mathlib

open scoped BigOperators
namespace ExplicitTensorBarrier694.Explicit.Supplement

/-- Lovitz, STOC 2027 submission #694 (October 2026), Lemma 5.4, p.16 (standing context
of §5, p.15: n = 2p+1 ≥ 3). If scalars c_J indexed by the (p+1)-subsets of [n] satisfy
Σ_{i∉I} c_{I∪{i}} = 0 for all p-subsets I ⊆ [n], then every c_J = 0. The n elements of
[n] are indexed by `Fin (2p+1)`; `c` is read only on (p+1)-subsets. -/
theorem _root_.solution (p : ℕ) (hp : 1 ≤ p) (c : Finset (Fin (2 * p + 1)) → ℂ)
    (hc : ∀ I : Finset (Fin (2 * p + 1)), I.card = p →
      ∑ i ∈ Iᶜ, c (insert i I) = 0) :
    ∀ J : Finset (Fin (2 * p + 1)), J.card = p + 1 → c J = 0 := by
  classical
  intro J hJ
  set S : ℕ → ℂ := fun k => ∑ K ∈ (Finset.univ.powersetCard (p+1) : Finset (Finset (Fin (2*p+1)))).filter (fun K => (K ∩ J).card = k), c K with hS
  have hS0 : S 0 = 0 := by
    refine Finset.sum_eq_zero fun K hK => ?_
    exfalso
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hK
    have h1 := Finset.card_union_add_card_inter K J
    have h2 : (K ∪ J).card ≤ 2*p+1 := le_trans (Finset.card_le_univ _) (by simp)
    omega
  have key : ∀ k, ((p+1-k : ℕ) : ℂ) * S k + ((k+1 : ℕ) : ℂ) * S (k+1) = 0 := by
    intro k
    set 𝒦 := (Finset.univ.powersetCard (p+1) : Finset (Finset (Fin (2*p+1)))) with h𝒦
    set ℐ := (Finset.univ.powersetCard p : Finset (Finset (Fin (2*p+1)))).filter (fun I => (I ∩ J).card = k) with hℐ
    have h0 : ∑ I ∈ ℐ, ∑ i ∈ Iᶜ, c (insert i I) = 0 := by
      refine Finset.sum_eq_zero fun I hI => hc I ?_
      rw [hℐ, Finset.mem_filter, Finset.mem_powersetCard] at hI; exact hI.1.2
    have hswap : ∑ I ∈ ℐ, ∑ i ∈ Iᶜ, c (insert i I) = ∑ K ∈ 𝒦, ∑ x ∈ K.filter (fun x => ((K.erase x) ∩ J).card = k), c K := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_bij' (fun a _ => ⟨insert a.2 a.1, a.2⟩) (fun b _ => ⟨b.1.erase b.2, b.2⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨I, i⟩ h
        simp only [Finset.mem_sigma, hℐ, h𝒦, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_compl] at h ⊢
        obtain ⟨⟨⟨_, hI⟩, hk⟩, hi⟩ := h
        refine ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem hi, hI]⟩, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.erase_insert hi]; exact hk
      · rintro ⟨K, x⟩ h
        simp only [Finset.mem_sigma, hℐ, h𝒦, Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_compl] at h ⊢
        obtain ⟨⟨_, hK⟩, hx, hk⟩ := h
        refine ⟨⟨⟨Finset.subset_univ _, by rw [Finset.card_erase_of_mem hx, hK]; omega⟩, hk⟩, Finset.notMem_erase _ _⟩
      · rintro ⟨I, i⟩ h
        simp only [Finset.mem_sigma, Finset.mem_compl] at h
        simp [Finset.erase_insert h.2]
      · rintro ⟨K, x⟩ h
        simp only [Finset.mem_sigma, Finset.mem_filter] at h
        simp [Finset.insert_erase h.2.1]
      · intro a _; rfl
    have hcount : ∀ K ∈ 𝒦, ((K.filter (fun x => ((K.erase x) ∩ J).card = k)).card : ℂ)
        = (if (K ∩ J).card = k then ((p+1-k : ℕ) : ℂ) else 0) + (if (K ∩ J).card = k+1 then ((k+1 : ℕ) : ℂ) else 0) := by
      intro K hK
      rw [h𝒦, Finset.mem_powersetCard] at hK
      have hin : ∀ x ∈ K, x ∈ J → ((K.erase x) ∩ J).card = (K ∩ J).card - 1 := by
        intro x hx hxJ
        rw [Finset.erase_inter, Finset.card_erase_of_mem (Finset.mem_inter.2 ⟨hx, hxJ⟩)]
      have hout : ∀ x ∈ K, x ∉ J → ((K.erase x) ∩ J).card = (K ∩ J).card := by
        intro x _ hxJ
        rw [Finset.erase_inter, Finset.erase_eq_of_notMem (fun h => hxJ (Finset.mem_inter.1 h).2)]
      by_cases h1 : (K ∩ J).card = k
      · rw [if_pos h1, if_neg (by omega), add_zero]
        have : K.filter (fun x => ((K.erase x) ∩ J).card = k) = K \ J := by
          ext x
          rw [Finset.mem_filter, Finset.mem_sdiff]
          constructor
          · rintro ⟨hx, h⟩
            refine ⟨hx, fun hxJ => ?_⟩
            rw [hin x hx hxJ] at h
            have : 0 < (K ∩ J).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hx, hxJ⟩⟩
            omega
          · rintro ⟨hx, hxJ⟩
            exact ⟨hx, by rw [hout x hx hxJ, h1]⟩
        rw [this]
        have h2 := Finset.card_sdiff_add_card_inter K J
        congr 1; omega
      · by_cases h2 : (K ∩ J).card = k+1
        · rw [if_neg h1, if_pos h2, zero_add]
          have : K.filter (fun x => ((K.erase x) ∩ J).card = k) = K ∩ J := by
            ext x
            rw [Finset.mem_filter, Finset.mem_inter]
            constructor
            · rintro ⟨hx, h⟩
              refine ⟨hx, by_contra fun hxJ => ?_⟩
              rw [hout x hx hxJ] at h; exact h1 h
            · rintro ⟨hx, hxJ⟩
              exact ⟨hx, by rw [hin x hx hxJ, h2]; omega⟩
          rw [this, h2]
        · rw [if_neg h1, if_neg h2, add_zero]
          have : K.filter (fun x => ((K.erase x) ∩ J).card = k) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro x hx h
            by_cases hxJ : x ∈ J
            · rw [hin x hx hxJ] at h
              have : 0 < (K ∩ J).card := Finset.card_pos.2 ⟨x, Finset.mem_inter.2 ⟨hx, hxJ⟩⟩
              omega
            · rw [hout x hx hxJ] at h; exact h1 h
          rw [this]; simp
    rw [hswap] at h0
    have : ∑ K ∈ 𝒦, ∑ x ∈ K.filter (fun x => ((K.erase x) ∩ J).card = k), c K
        = ((p+1-k : ℕ) : ℂ) * S k + ((k+1 : ℕ) : ℂ) * S (k+1) := by
      simp only [hS, ← h𝒦, Finset.sum_filter (s := 𝒦), Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun K hK => ?_
      rw [Finset.sum_const, nsmul_eq_mul, hcount K hK, add_mul]
      congr 1 <;> split <;> simp
    rw [← this]; exact h0
  have hall : ∀ k, k ≤ p+1 → S k = 0 := by
    intro k
    induction k with
    | zero => exact fun _ => hS0
    | succ k ih =>
      intro hk
      have h := key k
      rw [ih (by omega), mul_zero, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k))
  have hlast : S (p+1) = c J := by
    have : (Finset.univ.powersetCard (p+1) : Finset (Finset (Fin (2*p+1)))).filter (fun K => (K ∩ J).card = p+1) = {J} := by
      ext K
      rw [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, hK⟩, h⟩
        have h1 : K ∩ J = K := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        have h2 : K ⊆ J := h1 ▸ Finset.inter_subset_right
        exact Finset.eq_of_subset_of_card_le h2 (by omega)
      · rintro rfl
        exact ⟨⟨Finset.subset_univ _, hJ⟩, by rw [Finset.inter_self, hJ]⟩
    simp only [hS, this, Finset.sum_singleton]
  rw [← hlast]; exact hall _ le_rfl


end ExplicitTensorBarrier694.Explicit.Supplement

