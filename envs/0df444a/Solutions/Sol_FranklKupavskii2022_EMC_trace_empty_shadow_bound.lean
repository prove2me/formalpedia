-- Prove2me | solution 1 for FranklKupavskii2022.EMC.trace_empty_shadow_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:03:45.132987+00:00
-- url     : https://prove2.me/submissions/9cc6ba5e-bc85-423b-9141-97c802d75ff4

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_matchingNumber
import Definitions.Def_FranklKupavskii2022_EMC_IsInitial
import Definitions.Def_FranklKupavskii2022_EMC_trace

open FinsetFamily

namespace FranklKupavskii2022.EMC

open Finset

/-- Local LYM by double counting, for a `k`-uniform family on a ground set `X`. -/
theorem aux_emc_dc (X : Finset ℕ) (k : ℕ) (G : Finset (Finset ℕ))
    (hG : ∀ A ∈ G, A ⊆ X ∧ A.card = k) :
    G.card * k ≤ (∂ G).card * (X.card - k + 1) := by
  classical
  refine card_mul_le_card_mul' (fun (H A : Finset ℕ) => H ⊆ A) (fun A hA => ?_) (fun H hH => ?_)
  · rw [← (hG A hA).2, ← card_image_of_injOn A.erase_injOn]
    refine card_le_card ?_
    intro H hH
    simp only [mem_image] at hH
    obtain ⟨a, ha, rfl⟩ := hH
    rw [mem_bipartiteBelow]
    exact ⟨erase_mem_shadow hA ha, erase_subset _ _⟩
  · obtain ⟨A0, hA0, x, hx, rfl⟩ := mem_shadow_iff.1 hH
    have hX0 := hG A0 hA0
    have hsub : A0.erase x ⊆ X := (erase_subset _ _).trans hX0.1
    have hcard : (A0.erase x).card = k - 1 := by rw [card_erase_of_mem hx, hX0.2]
    have hk : 1 ≤ k := by
      rw [← hX0.2]; exact card_pos.2 ⟨x, hx⟩
    calc (G.bipartiteAbove (fun H A => H ⊆ A) (A0.erase x)).card
        ≤ ((X \ A0.erase x).image (fun a => insert a (A0.erase x))).card := by
          apply card_le_card
          intro A hA
          rw [mem_bipartiteAbove] at hA
          obtain ⟨hAG, hHA⟩ := hA
          have hAX := hG A hAG
          obtain ⟨a, ha, rfl⟩ := exists_eq_insert_iff.2 ⟨hHA, by omega⟩
          rw [mem_image]
          exact ⟨a, mem_sdiff.2 ⟨hAX.1 (mem_insert_self _ _), ha⟩, rfl⟩
      _ ≤ (X \ A0.erase x).card := card_image_le
      _ = X.card - (k - 1) := by rw [card_sdiff_of_subset hsub, hcard]
      _ ≤ X.card - k + 1 := tsub_tsub_le_tsub_add

theorem aux_emc_filter_card (A : Finset ℕ) (x y t : ℕ) (hx : x ∈ A) (hy : y ∉ A)
    (hxy : y < x) :
    (A.filter (· ≤ t)).card ≤ ((insert y (A.erase x)).filter (· ≤ t)).card := by
  rw [filter_insert, filter_erase]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp [hy])]
    have := pred_card_le_card_erase (s := A.filter (· ≤ t)) (a := x)
    omega
  · have hx' : x ∉ A.filter (· ≤ t) := by
      simp only [mem_filter, not_and, not_le]
      intro _
      omega
    rw [erase_eq_of_notMem hx']

theorem aux_emc_sort_le (A B : Finset ℕ) (hc : B.card = A.card)
    (h : ∀ t, (A.filter (· ≤ t)).card ≤ (B.filter (· ≤ t)).card) :
    List.Forall₂ (· ≤ ·) B.sort A.sort := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hc], fun i h1 h2 => ?_⟩
  have hA : A.card = A.card := rfl
  have hi : i < A.card := by simpa using h2
  have e1 : B.sort.get ⟨i, h1⟩ = B.orderEmbOfFin hc ⟨i, hi⟩ := by
    rw [orderEmbOfFin_apply]; rfl
  have e2 : A.sort.get ⟨i, h2⟩ = A.orderEmbOfFin hA ⟨i, hi⟩ := by
    rw [orderEmbOfFin_apply]; rfl
  rw [e1, e2]
  generalize (⟨i, hi⟩ : Fin A.card) = j
  by_contra hlt
  push Not at hlt
  have h3 := h (A.orderEmbOfFin hA j)
  have h4 : (Finset.Iic j).map (A.orderEmbOfFin hA).toEmbedding ⊆
      A.filter (· ≤ A.orderEmbOfFin hA j) := by
    intro z hz
    simp only [mem_map, mem_Iic] at hz
    obtain ⟨l, hl, rfl⟩ := hz
    rw [mem_filter]
    exact ⟨orderEmbOfFin_mem _ _ _, (A.orderEmbOfFin hA).le_iff_le.2 hl⟩
  have h5 : B.filter (· ≤ A.orderEmbOfFin hA j) ⊆
      (Finset.Iio j).map (B.orderEmbOfFin hc).toEmbedding := by
    intro z hz
    rw [mem_filter] at hz
    have : z ∈ Set.range (B.orderEmbOfFin hc) := by
      rw [range_orderEmbOfFin]; exact hz.1
    obtain ⟨l, rfl⟩ := this
    simp only [mem_map, mem_Iio]
    refine ⟨l, ?_, rfl⟩
    have : B.orderEmbOfFin hc l < B.orderEmbOfFin hc j := lt_of_le_of_lt hz.2 hlt
    exact (B.orderEmbOfFin hc).lt_iff_lt.1 this
  have c1 := card_le_card h4
  have c2 := card_le_card h5
  simp only [card_map, Fin.card_Iic, Fin.card_Iio] at c1 c2
  omega

theorem aux_emc_prec (A : Finset ℕ) (x y : ℕ) (hx : x ∈ A) (hy : y ∉ A) (hxy : y < x) :
    Precedes (insert y (A.erase x)) A := by
  refine ⟨aux_emc_sort_le A _ ?_ (fun t => aux_emc_filter_card A x y t hx hy hxy), ?_⟩
  · rw [card_insert_of_notMem (by simp [hy]), card_erase_of_mem hx]
    have := card_pos.2 ⟨x, hx⟩
    omega
  · intro h
    apply hy
    rw [← h]
    exact mem_insert_self _ _

theorem aux_emc_main (s : ℕ) (hs : 1 ≤ s) (X : Finset ℕ) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (G : Finset (Finset ℕ)),
      (∀ A ∈ G, A ⊆ X ∧ A.card = k) →
      (∀ A ∈ G, ∀ x ∈ A, ∀ y ∈ X, y < x → y ∉ A → insert y (A.erase x) ∈ G) →
      (∀ f : Fin (s + 1) → Finset ℕ, (∀ i, f i ∈ G) →
        (∀ i j, i ≠ j → Disjoint (f i) (f j)) → False) →
      G.card ≤ s * (∂ G).card := by
  induction X using Finset.induction_on_max with
  | empty =>
    intro k hk G hG _ _
    have : G = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro A hA
      have h1 := hG A hA
      have h2 : A = ∅ := subset_empty.1 h1.1
      rw [h2, card_empty] at h1
      omega
    simp [this]
  | insert N X' hlt ih =>
    intro k hk G hG hsh hnm
    have hNX : N ∉ X' := fun h => lt_irrefl _ (hlt N h)
    by_cases hsmall : (insert N X').card < (s + 1) * k
    · have h1 := aux_emc_dc (insert N X') k G hG
      have h2 : (insert N X').card - k + 1 ≤ s * k := by
        have : (s + 1) * k = s * k + k := by ring
        rw [this] at hsmall
        have hsk : 1 * 1 ≤ s * k := Nat.mul_le_mul hs hk
        omega
      have h3 : G.card * k ≤ (∂ G).card * (s * k) := h1.trans (Nat.mul_le_mul_left _ h2)
      have h4 : G.card * k ≤ (s * (∂ G).card) * k := by
        calc G.card * k ≤ (∂ G).card * (s * k) := h3
          _ = (s * (∂ G).card) * k := by ring
      exact Nat.le_of_mul_le_mul_right h4 (by omega)
    · push Not at hsmall
      rcases Nat.lt_or_ge k 2 with hk1 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        by_cases hGe : G = ∅
        · simp [hGe]
        · have hsh1 : ∅ ∈ ∂ G := by
            obtain ⟨A, hA⟩ := nonempty_iff_ne_empty.2 hGe
            obtain ⟨a, ha⟩ := card_eq_one.1 (hG A hA).2
            rw [mem_shadow_iff]
            exact ⟨A, hA, a, by simp [ha], by simp [ha]⟩
          have hsc : 1 ≤ (∂ G).card := card_pos.2 ⟨∅, hsh1⟩
          have hGs : G.card ≤ s := by
            by_contra hc
            push Not at hc
            obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset
              (α := Fin (s + 1)) (s := G) (by simpa using hc)
            have hfG : ∀ i, f i ∈ G := fun i => hf ⟨i, rfl⟩
            apply hnm f hfG
            intro i j hij
            obtain ⟨a, ha⟩ := card_eq_one.1 (hG _ (hfG i)).2
            obtain ⟨b, hb⟩ := card_eq_one.1 (hG _ (hfG j)).2
            rw [ha, hb, disjoint_singleton]
            intro hab
            apply hij
            apply f.injective
            rw [ha, hb, hab]
          nlinarith
      · have hcard := card_memberSubfamily_add_card_nonMemberSubfamily N G
        -- the two subfamilies
        have hG1X : ∀ A ∈ G.nonMemberSubfamily N, A ⊆ X' ∧ A.card = k := by
          intro A hA
          rw [mem_nonMemberSubfamily] at hA
          have := hG A hA.1
          exact ⟨(subset_insert_iff_of_notMem hA.2).1 this.1, this.2⟩
        have hG2X : ∀ C ∈ G.memberSubfamily N, C ⊆ X' ∧ C.card = k - 1 := by
          intro C hC
          rw [mem_memberSubfamily] at hC
          have := hG _ hC.1
          refine ⟨?_, ?_⟩
          · exact (subset_insert_iff_of_notMem hC.2).1 ((subset_insert _ _).trans this.1)
          · have h2 := this.2
            rw [card_insert_of_notMem hC.2] at h2
            omega
        have hG1 : (G.nonMemberSubfamily N).card ≤ s * (∂ (G.nonMemberSubfamily N)).card := by
          refine ih k hk _ hG1X ?_ ?_
          · intro A hA x hx y hy hyx hyA
            rw [mem_nonMemberSubfamily] at hA ⊢
            refine ⟨hsh A hA.1 x hx y (mem_insert_of_mem hy) hyx hyA, ?_⟩
            rw [mem_insert]
            push Not
            exact ⟨fun h => hNX (h ▸ hy), fun h => hA.2 (mem_of_mem_erase h)⟩
          · intro f hf hd
            exact hnm f (fun i => (mem_nonMemberSubfamily.1 (hf i)).1) hd
        have hG2 : (G.memberSubfamily N).card ≤ s * (∂ (G.memberSubfamily N)).card := by
          refine ih (k - 1) (by omega) _ hG2X ?_ ?_
          · intro C hC x hx y hy hyx hyC
            rw [mem_memberSubfamily] at hC ⊢
            have hyN : y ≠ N := fun h => hNX (h ▸ hy)
            have hxN : x ≠ N := fun h => hC.2 (h ▸ hx)
            have h1 := hsh (insert N C) hC.1 x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)
              hyx (by rw [mem_insert]; push Not; exact ⟨hyN, hyC⟩)
            rw [erase_insert_of_ne (Ne.symm hxN), insert_comm] at h1
            refine ⟨h1, ?_⟩
            rw [mem_insert]
            push Not
            exact ⟨Ne.symm hyN, fun h => hC.2 (mem_of_mem_erase h)⟩
          · intro f hf hd
            have hfX : ∀ i, f i ⊆ X' ∧ (f i).card = k - 1 := fun i => hG2X (f i) (hf i)
            have hU : (Finset.univ.biUnion f).card ≤ (s + 1) * (k - 1) := by
              calc (Finset.univ.biUnion f).card ≤ ∑ i, (f i).card := card_biUnion_le
                _ = ∑ _i : Fin (s + 1), (k - 1) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    exact (hfX i).2
                _ = (s + 1) * (k - 1) := by simp
            have hT : s + 1 ≤ (insert N (X' \ Finset.univ.biUnion f)).card := by
              rw [card_insert_of_notMem (by simp [hNX])]
              have h1 := le_card_sdiff (Finset.univ.biUnion f) X'
              have h2 : (insert N X').card = X'.card + 1 := card_insert_of_notMem hNX
              have h3 : (s + 1) * k = (s + 1) * (k - 1) + (s + 1) := by
                have : k = (k - 1) + 1 := by omega
                conv_lhs => rw [this]
                ring
              omega
            obtain ⟨t, ht⟩ := Function.Embedding.exists_of_card_le_finset
              (α := Fin (s + 1)) (s := insert N (X' \ Finset.univ.biUnion f)) (by simpa using hT)
            have htT : ∀ i, t i ∈ insert N (X' \ Finset.univ.biUnion f) := fun i => ht ⟨i, rfl⟩
            have htf : ∀ i j, t i ∉ f j := by
              intro i j hm
              rcases mem_insert.1 (htT i) with h | h
              · rw [h] at hm
                exact (mem_memberSubfamily.1 (hf j)).2 hm
              · exact (mem_sdiff.1 h).2 (mem_biUnion.2 ⟨j, mem_univ _, hm⟩)
            apply hnm (fun i => insert (t i) (f i))
            · intro i
              have h1 := mem_memberSubfamily.1 (hf i)
              rcases mem_insert.1 (htT i) with h | h
              · rw [h]
                exact h1.1
              · rw [mem_sdiff] at h
                have hti : t i ∉ f i := htf i i
                have hlt' : t i < N := hlt _ h.1
                have := hsh (insert N (f i)) h1.1 N (mem_insert_self _ _) (t i)
                  (mem_insert_of_mem h.1) hlt'
                  (by rw [mem_insert]; push Not; exact ⟨ne_of_lt hlt', hti⟩)
                rwa [erase_insert h1.2] at this
            · intro i j hij
              rw [disjoint_left]
              intro z hz1 hz2
              rw [mem_insert] at hz1 hz2
              rcases hz1 with rfl | hz1 <;> rcases hz2 with h | hz2
              · exact hij (t.injective h)
              · exact htf i j hz2
              · rw [h] at hz1
                exact htf j i hz1
              · exact disjoint_left.1 (hd i j hij) hz1 hz2
        -- shadow inequality
        have hsh2 : (∂ (G.nonMemberSubfamily N)).card + (∂ (G.memberSubfamily N)).card
            ≤ (∂ G).card := by
          have hN1 : ∀ B ∈ ∂ (G.nonMemberSubfamily N), N ∉ B := by
            intro B hB
            obtain ⟨A, hA, a, _, rfl⟩ := mem_shadow_iff.1 hB
            exact fun h => (mem_nonMemberSubfamily.1 hA).2 (mem_of_mem_erase h)
          have hN2 : ∀ B ∈ ∂ (G.memberSubfamily N), N ∉ B := by
            intro B hB
            obtain ⟨C, hC, a, _, rfl⟩ := mem_shadow_iff.1 hB
            exact fun h => (mem_memberSubfamily.1 hC).2 (mem_of_mem_erase h)
          have hinj : Set.InjOn (insert N) (↑(∂ (G.memberSubfamily N)) : Set (Finset ℕ)) := by
            intro B1 hB1 B2 hB2 heq
            have n1 := hN2 B1 hB1
            have n2 := hN2 B2 hB2
            rw [← erase_insert n1, ← erase_insert n2]
            rw [heq]
          rw [← card_image_of_injOn hinj, ← card_union_of_disjoint]
          · apply card_le_card
            intro B hB
            rcases mem_union.1 hB with h | h
            · exact shadow_monotone (fun A hA => (mem_nonMemberSubfamily.1 hA).1) h
            · obtain ⟨B', hB', rfl⟩ := mem_image.1 h
              obtain ⟨C, hC, x, hx, rfl⟩ := mem_shadow_iff.1 hB'
              rw [mem_memberSubfamily] at hC
              rw [mem_shadow_iff]
              have hxN : x ≠ N := fun h => hC.2 (h ▸ hx)
              refine ⟨insert N C, hC.1, x, mem_insert_of_mem hx, ?_⟩
              rw [erase_insert_of_ne (Ne.symm hxN)]
          · rw [disjoint_left]
            intro B hB1 hB2
            obtain ⟨B', _, rfl⟩ := mem_image.1 hB2
            exact hN1 _ hB1 (mem_insert_self _ _)
        nlinarith

end FranklKupavskii2022.EMC

open FranklKupavskii2022.EMC

theorem solution (n k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) (hn : k * (s + 1) ≤ n)
    (F : Finset (Finset ℕ)) (hF : F ⊆ (Finset.Icc 1 n).powersetCard k) (hinit : IsInitial n k F)
    (hν : matchingNumber F ≤ s) :
    (trace s F ∅).card ≤ s * (∂ (trace s F ∅)).card := by
  have htr : trace s F ∅ = F.filter (fun A => A ∩ Finset.Icc 1 (s + 1) = ∅) := by
    unfold trace
    simp
  rw [htr]
  apply aux_emc_main s hs (Finset.Icc (s + 2) n) k hk
  · intro A hA
    rw [Finset.mem_filter] at hA
    have := Finset.mem_powersetCard.1 (hF hA.1)
    refine ⟨?_, this.2⟩
    intro a ha
    have h1 := Finset.mem_Icc.1 (this.1 ha)
    have h2 : a ∉ Finset.Icc 1 (s + 1) := fun h => by
      have : a ∈ A ∩ Finset.Icc 1 (s + 1) := Finset.mem_inter.2 ⟨ha, h⟩
      rw [hA.2] at this
      simp at this
    rw [Finset.mem_Icc] at h2 ⊢
    omega
  · intro A hA x hx y hy hyx hyA
    rw [Finset.mem_filter] at hA ⊢
    have hAp := Finset.mem_powersetCard.1 (hF hA.1)
    have hy' := Finset.mem_Icc.1 hy
    refine ⟨hinit _ ?_ A hA.1 (aux_emc_prec A x y hx hyA hyx), ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · rw [Finset.mem_Icc]; omega
        · exact hAp.1 (Finset.mem_of_mem_erase hz)
      · rw [Finset.card_insert_of_notMem (by simp [hyA]), Finset.card_erase_of_mem hx, hAp.2]
        have := Finset.card_pos.2 ⟨x, hx⟩
        omega
    · rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_Icc] at hz
      rcases hz with ⟨rfl | hz, hz2⟩
      · omega
      · have : z ∈ A ∩ Finset.Icc 1 (s + 1) :=
          Finset.mem_inter.2 ⟨Finset.mem_of_mem_erase hz, Finset.mem_Icc.2 hz2⟩
        rw [hA.2] at this
        simp at this
  · intro f hf hd
    have hne : ∀ i, (f i).Nonempty := by
      intro i
      have := Finset.mem_powersetCard.1 (hF (Finset.mem_filter.1 (hf i)).1)
      rw [← Finset.card_pos, this.2]
      omega
    have hinj : Function.Injective f := by
      intro i j hij
      by_contra hne'
      have h1 := hd i j hne'
      rw [hij] at h1
      have h2 : f j = ∅ := disjoint_self.1 h1
      obtain ⟨z, hz⟩ := hne j
      rw [h2] at hz
      simp at hz
    unfold matchingNumber at hν
    rw [Finset.sup_le_iff] at hν
    have := hν (Finset.univ.image f) (by
      simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · intro A hA
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hA
        exact (Finset.mem_filter.1 (hf i)).1
      · intro A hA B hB hAB
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hA
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hB
        exact hd i j (fun h => hAB (h ▸ rfl)))
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this
    omega
