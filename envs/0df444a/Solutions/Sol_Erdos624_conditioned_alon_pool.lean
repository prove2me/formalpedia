-- Prove2me | solution 1 for Erdos624.conditioned_alon_pool
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T13:49:03.913085+00:00
-- url     : https://prove2.me/submissions/1232ae35-f07f-4cb5-bb35-09fc03b9e478

import Mathlib
open Finset

namespace E624R10A
open Finset

section
variable {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]

/-- Palette inequality, image-count form. -/
lemma palette_count (f : Finset U → C) (W : Finset U) (a b : U) (hab : a ≠ b)
    (ha : a ∉ W) (hb : b ∉ W) :
    #((insert a (insert b W)).powerset.image f) +
        #(W.powerset.image (fun A => f (insert a A)) ∩ W.powerset.image (fun A => f (insert b A))) ≤
      2 * 2 ^ #W + #(W.powerset.image (fun A => f (insert a A))) +
        #(W.powerset.image (fun A => f (insert b A))) := by
  set Sa := W.powerset.image (fun A => f (insert a A))
  set Sb := W.powerset.image (fun A => f (insert b A))
  have hsub : (insert a (insert b W)).powerset.image f ⊆
      (W.powerset.image f ∪ W.powerset.image (fun A => f (insert a (insert b A)))) ∪
        (Sa ∪ Sb) := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hx
    rw [mem_powerset] at hA
    set A0 := (A.erase a).erase b with hA0
    have hA0W : A0 ⊆ W := by
      intro y hy
      rw [hA0, mem_erase, mem_erase] at hy
      have := hA hy.2.2
      rw [mem_insert, mem_insert] at this
      rcases this with h | h | h
      · exact absurd h hy.2.1
      · exact absurd h hy.1
      · exact h
    have hm : A0 ∈ W.powerset := mem_powerset.2 hA0W
    by_cases haA : a ∈ A <;> by_cases hbA : b ∈ A
    · have : A = insert a (insert b A0) := by
        ext y; simp only [hA0, mem_insert, mem_erase]
        constructor
        · intro hy; by_cases h1 : y = a; · exact Or.inl h1
          by_cases h2 : y = b; · exact Or.inr (Or.inl h2)
          exact Or.inr (Or.inr ⟨h2, h1, hy⟩)
        · rintro (rfl | rfl | ⟨_, _, hy⟩) <;> assumption
      rw [this]
      exact mem_union_left _ (mem_union_right _ (mem_image.2 ⟨A0, hm, rfl⟩))
    · have : A = insert a A0 := by
        ext y; simp only [hA0, mem_insert, mem_erase]
        constructor
        · intro hy; by_cases h1 : y = a; · exact Or.inl h1
          refine Or.inr ⟨?_, h1, hy⟩; rintro rfl; exact hbA hy
        · rintro (rfl | ⟨_, _, hy⟩) <;> assumption
      rw [this]
      exact mem_union_right _ (mem_union_left _ (mem_image.2 ⟨A0, hm, rfl⟩))
    · have : A = insert b A0 := by
        ext y; simp only [hA0, mem_insert, mem_erase]
        constructor
        · intro hy; by_cases h1 : y = b; · exact Or.inl h1
          refine Or.inr ⟨h1, ?_, hy⟩; rintro rfl; exact haA hy
        · rintro (rfl | ⟨_, _, hy⟩) <;> assumption
      rw [this]
      exact mem_union_right _ (mem_union_right _ (mem_image.2 ⟨A0, hm, rfl⟩))
    · have : A = A0 := by
        ext y; simp only [hA0, mem_erase]
        constructor
        · intro hy; refine ⟨?_, ?_, hy⟩ <;> rintro rfl <;> contradiction
        · rintro ⟨_, _, hy⟩; exact hy
      rw [this]
      exact mem_union_left _ (mem_union_left _ (mem_image.2 ⟨A0, hm, rfl⟩))
  have h1 := card_le_card hsub
  have h2 := card_union_le (W.powerset.image f ∪ W.powerset.image
    (fun A => f (insert a (insert b A)))) (Sa ∪ Sb)
  have h3 := card_union_le (W.powerset.image f) (W.powerset.image
    (fun A => f (insert a (insert b A))))
  have h4 : #(W.powerset.image f) ≤ 2 ^ #W := (card_image_le).trans (card_powerset W).le
  have h5 : #(W.powerset.image (fun A => f (insert a (insert b A)))) ≤ 2 ^ #W :=
    (card_image_le).trans (card_powerset W).le
  have h6 := card_union_add_card_inter Sa Sb
  omega

lemma pal_le (f : Finset U → C) (W : Finset U) (a : U) :
    #(W.powerset.image (fun A => f (insert a A))) ≤ 2 ^ #W :=
  (card_image_le).trans (card_powerset W).le

end

section
variable {C : Type*} [Fintype C] [DecidableEq C]

lemma card_inter_eq_sum (S T : Finset C) :
    (#(S ∩ T) : ℤ) = ∑ u, (if u ∈ S then (1 : ℤ) else 0) * (if u ∈ T then 1 else 0) := by
  have : S ∩ T = univ.filter (fun u => u ∈ S ∧ u ∈ T) := by ext u; simp
  rw [this, card_filter]; push_cast
  apply sum_congr rfl; intro u _
  by_cases h1 : u ∈ S <;> by_cases h2 : u ∈ T <;> simp [h1, h2]

lemma card_eq_sum (S : Finset C) : (#S : ℤ) = ∑ u, (if u ∈ S then (1 : ℤ) else 0) := by
  have : S = univ.filter (fun u => u ∈ S) := by ext u; simp
  conv_lhs => rw [this]
  rw [card_filter]; push_cast; rfl

end

section
variable {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

/-- Per-core averaged bound over an arbitrary pool `R` of extension points (disjoint from `W`). -/
lemma core_bound (f : Finset U → C) (W R : Finset U) (hRW : Disjoint R W)
    (hC : Fintype.card C = 4 * 2 ^ #W) (hv : 7 ≤ #R) :
    Fintype.card C * (#R * (#R - 1)) ≤
      32 * ∑ a ∈ R, ∑ b ∈ R.erase a,
        (Fintype.card C - #((insert a (insert b W)).powerset.image f)) := by
  set V := R with hV
  set q : ℕ := 2 ^ #W with hq
  set n := Fintype.card C with hn
  set v := #V with hvdef
  have hq0 : 0 < q := by positivity
  set s : U → ℤ := fun a => #(W.powerset.image (fun A => f (insert a A))) with hs
  set I : U → U → ℤ := fun a b => #(W.powerset.image (fun A => f (insert a A)) ∩
    W.powerset.image (fun A => f (insert b A))) with hI
  set x : C → U → ℤ := fun u a => if u ∈ W.powerset.image (fun A => f (insert a A)) then 1 else 0
    with hx
  set σ : ℤ := ∑ a ∈ V, s a with hσ
  set E2 : ℤ := ∑ u, (∑ a ∈ V, x u a) ^ 2 with hE2
  have hterm : ∀ a ∈ V, ∀ b ∈ V.erase a,
      (2 * (q : ℤ) - s a - s b + I a b) ≤
        ((n - #((insert a (insert b W)).powerset.image f) : ℕ) : ℤ) := by
    intro a ha b hb
    rw [mem_erase] at hb
    have haW : a ∉ W := fun h => disjoint_left.1 hRW ha h
    have hbW : b ∉ W := fun h => disjoint_left.1 hRW hb.2 h
    have hl := palette_count f W a b (Ne.symm hb.1) haW hbW
    have hle : #((insert a (insert b W)).powerset.image f) ≤ n := by
      rw [hn]; exact card_le_univ _
    rw [Nat.cast_sub hle]
    simp only [hs, hI]
    have : (n : ℤ) = 4 * q := by exact_mod_cast hC
    omega
  have hsum_le := sum_le_sum (fun a ha => sum_le_sum (hterm a ha))
  have hIself : ∀ a, I a a = s a := by intro a; simp [hI, hs]
  have hIsum : ∑ a ∈ V, ∑ b ∈ V, I a b = E2 := by
    calc ∑ a ∈ V, ∑ b ∈ V, I a b = ∑ a ∈ V, ∑ b ∈ V, ∑ u, x u a * x u b := by
          simp only [hI, card_inter_eq_sum, hx]
      _ = ∑ a ∈ V, ∑ u, ∑ b ∈ V, x u a * x u b := by
          apply sum_congr rfl; intro a _; rw [sum_comm]
      _ = ∑ u, ∑ a ∈ V, ∑ b ∈ V, x u a * x u b := by rw [sum_comm]
      _ = E2 := by simp only [hE2, sq, sum_mul_sum]
  have hσ2 : σ = ∑ u, ∑ a ∈ V, x u a := by
    simp only [hσ, hs, card_eq_sum, hx]; rw [sum_comm]
  have hLHS : ∑ a ∈ V, ∑ b ∈ V.erase a, (2 * (q : ℤ) - s a - s b + I a b) =
      2 * ((v : ℤ) - 1) * ((q : ℤ) * v - σ) + (E2 - σ) := by
    have h1 : ∀ a ∈ V, ∑ b ∈ V.erase a, (2 * (q : ℤ) - s a - s b + I a b) =
        (v : ℤ) * (2 * q - s a) - σ + ∑ b ∈ V, I a b - 2 * q + s a := by
      intro a ha
      rw [sum_erase_eq_sub ha, sum_add_distrib, sum_sub_distrib, sum_const, hIself]
      simp only [nsmul_eq_mul, hσ, hvdef]; ring
    rw [sum_congr rfl h1, ← hIsum]
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← hσ,
      ← hvdef]
    ring
  have hCS : σ ^ 2 ≤ (n : ℤ) * E2 := by
    rw [hσ2, hE2, hn, ← Finset.card_univ]
    exact sq_sum_le_card_mul_sum_sq
  have hsq : ∀ a, s a ≤ q := fun a => by simp only [hs]; exact_mod_cast pal_le f W a
  have hσle : σ ≤ (q : ℤ) * v := by
    calc σ ≤ ∑ a ∈ V, (q : ℤ) := sum_le_sum (fun a _ => hsq a)
      _ = q * v := by rw [sum_const, nsmul_eq_mul, hvdef]; ring
  have hnq : (n : ℤ) = 4 * q := by exact_mod_cast hC
  have hv7 : (7 : ℤ) ≤ v := by exact_mod_cast hv
  set T : ℤ := ∑ a ∈ V, ∑ b ∈ V.erase a,
        (((n - #((insert a (insert b W)).powerset.image f) : ℕ) : ℤ)) with hT
  have hTge : 2 * ((v : ℤ) - 1) * ((q : ℤ) * v - σ) + (E2 - σ) ≤ T := by
    rw [← hLHS]; exact hsum_le
  have hqpos : (0 : ℤ) < q := by exact_mod_cast hq0
  have key : (4 * q : ℤ) * (4 * q * (v * (v - 1))) ≤ (4 * q) * (32 * T) := by
    have hD : 0 ≤ (q : ℤ) * v - σ := by linarith
    have h4E : σ ^ 2 ≤ 4 * q * E2 := by rw [← hnq]; exact hCS
    nlinarith [mul_nonneg hD (by nlinarith : (0:ℤ) ≤ 6 * q * v - 4 * q), mul_nonneg hD hD,
      mul_nonneg (mul_nonneg hqpos.le hqpos.le) (by nlinarith : (0:ℤ) ≤ v * (v - 7))]
  have key2 : (4 * q * (v * (v - 1)) : ℤ) ≤ 32 * T :=
    le_of_mul_le_mul_left key (by positivity)
  have hv1 : 1 ≤ v := by omega
  have : ((n * (v * (v - 1)) : ℕ) : ℤ) ≤ ((32 * ∑ a ∈ V, ∑ b ∈ V.erase a,
        (n - #((insert a (insert b W)).powerset.image f)) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hv1]
    rw [hnq]
    simpa [hT] using key2
  exact_mod_cast this

end

section
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Double counting of presentations `Y = W ∪ {a, b}` inside a pool `V`. -/
lemma presentation_sum_pool (V : Finset U) (m : ℕ) (F : Finset U → U → U → ℕ) :
    ∑ W ∈ powersetCard m V, ∑ a ∈ V \ W, ∑ b ∈ (V \ W).erase a,
      F (insert a (insert b W)) a b =
    ∑ Y ∈ powersetCard (m + 2) V, ∑ a ∈ Y, ∑ b ∈ Y.erase a, F Y a b := by
  set R1 : Finset (Finset U × U × U) := univ.filter
    (fun p => p.1 ⊆ V ∧ #p.1 = m ∧ (p.2.1 ∈ V ∧ p.2.1 ∉ p.1) ∧ p.2.2 ≠ p.2.1 ∧
      (p.2.2 ∈ V ∧ p.2.2 ∉ p.1)) with hR1
  set R2 : Finset (Finset U × U × U) := univ.filter
    (fun p => p.1 ⊆ V ∧ #p.1 = m + 2 ∧ p.2.1 ∈ p.1 ∧ p.2.2 ≠ p.2.1 ∧ p.2.2 ∈ p.1) with hR2
  have e1 : ∑ W ∈ powersetCard m V, ∑ a ∈ V \ W, ∑ b ∈ (V \ W).erase a,
      F (insert a (insert b W)) a b =
        ∑ p ∈ R1, F (insert p.2.1 (insert p.2.2 p.1)) p.2.1 p.2.2 := by
    rw [Finset.sum_finset_product (r := R1) (s := powersetCard m V)
      (t := fun W => ((V \ W) ×ˢ univ).filter (fun ab => ab.2 ∈ (V \ W).erase ab.1))]
    · apply Finset.sum_congr rfl
      intro W _
      rw [Finset.sum_finset_product (r := ((V \ W) ×ˢ univ).filter
        (fun ab => ab.2 ∈ (V \ W).erase ab.1)) (s := V \ W)
        (t := fun a => (V \ W).erase a)]
      intro p; simp only [mem_filter, mem_product, mem_univ, and_true]
    · intro p
      simp only [hR1, mem_filter, mem_univ, true_and, mem_powersetCard,
        mem_product, mem_sdiff, mem_erase, and_true]
      tauto
  have e2 : ∑ Y ∈ powersetCard (m + 2) V, ∑ a ∈ Y, ∑ b ∈ Y.erase a, F Y a b =
      ∑ p ∈ R2, F p.1 p.2.1 p.2.2 := by
    rw [Finset.sum_finset_product (r := R2) (s := powersetCard (m + 2) V)
      (t := fun Y => (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))]
    · apply Finset.sum_congr rfl
      intro Y hY
      rw [Finset.sum_finset_product (r := (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))
        (s := Y) (t := fun a => Y.erase a)]
      intro p; simp only [mem_filter, mem_product, mem_univ, and_true]
    · intro p
      simp only [hR2, mem_filter, mem_univ, true_and, mem_powersetCard,
        mem_product, mem_erase, and_true]
      tauto
  rw [e1, e2]
  apply Finset.sum_nbij' (fun p => (insert p.2.1 (insert p.2.2 p.1), p.2.1, p.2.2))
    (fun p => ((p.1.erase p.2.1).erase p.2.2, p.2.1, p.2.2))
  · rintro ⟨W, a, b⟩ h
    simp only [hR1, hR2, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨h0, h1, ⟨h2V, h2⟩, h4, ⟨h3V, h3⟩⟩ := h
    refine ⟨?_, ?_, mem_insert_self _ _, h4, mem_insert_of_mem (mem_insert_self _ _)⟩
    · intro x hx; simp only [mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · exact h2V
      · exact h3V
      · exact h0 hx
    rw [card_insert_of_notMem, card_insert_of_notMem h3, h1]
    simp [h2, Ne.symm h4]
  · rintro ⟨Y, a, b⟩ h
    simp only [hR1, hR2, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨h0, h1, h2, h4, h3⟩ := h
    refine ⟨fun x hx => h0 (mem_of_mem_erase (mem_of_mem_erase hx)), ?_,
      ⟨h0 h2, by simp⟩, h4, ⟨h0 h3, by simp⟩⟩
    rw [card_erase_of_mem (mem_erase.2 ⟨h4, h3⟩), card_erase_of_mem h2, h1]; rfl
  · rintro ⟨W, a, b⟩ h
    simp only [hR1, mem_filter, mem_univ, true_and] at h
    obtain ⟨h0, h1, ⟨_, h2⟩, h4, ⟨_, h3⟩⟩ := h
    simp only [Prod.mk.injEq, and_true]
    ext x; simp only [mem_erase, mem_insert]
    constructor
    · rintro ⟨hb, ha, (rfl | rfl | hx)⟩ <;> tauto
    · intro hx; refine ⟨?_, ?_, Or.inr (Or.inr hx)⟩ <;> rintro rfl <;> contradiction
  · rintro ⟨Y, a, b⟩ h
    simp only [hR2, mem_filter, mem_univ, true_and] at h
    obtain ⟨h0, h1, h2, h4, h3⟩ := h
    simp only [Prod.mk.injEq, and_true]
    ext x; simp only [mem_erase, mem_insert]
    constructor
    · rintro (rfl | rfl | ⟨_, _, hx⟩) <;> assumption
    · intro hx
      by_cases hxa : x = a
      · exact Or.inl hxa
      · by_cases hxb : x = b
        · exact Or.inr (Or.inl hxb)
        · exact Or.inr (Or.inr ⟨hxb, hxa, hx⟩)
  · rintro ⟨W, a, b⟩ _; rfl

/-- Number of ordered pairs of distinct elements of `Y \ B`, written as a sum over `Y`. -/
lemma pair_count (B Y : Finset U) (G : ℕ) :
    ∑ a ∈ Y, ∑ b ∈ Y.erase a, (if a ∉ B ∧ b ∉ B then G else 0) =
      #(Y \ B) * (#(Y \ B) - 1) * G := by
  have h1 : ∀ a ∈ Y, ∑ b ∈ Y.erase a, (if a ∉ B ∧ b ∉ B then G else 0) =
      if a ∉ B then (#(Y \ B) - 1) * G else 0 := by
    intro a ha
    by_cases haB : a ∉ B
    · rw [sum_congr rfl (g := fun b => if b ∉ B then G else 0) (fun b _ => by simp [haB])]
      simp only [haB, not_false_eq_true, if_true]
      rw [← sum_filter, sum_const, smul_eq_mul]
      congr 1
      have : (Y.erase a).filter (fun b => b ∉ B) = (Y \ B).erase a := by
        ext x; simp [mem_sdiff]; tauto
      rw [this, card_erase_of_mem (by simp [mem_sdiff, ha, haB])]
    · simp [haB]
  rw [sum_congr rfl h1, ← sum_filter, sum_const, smul_eq_mul]
  have : Y.filter (fun a => a ∉ B) = Y \ B := by ext x; simp [mem_sdiff]
  rw [this]; ring

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Conditioned Alon, pool form, general colour type. -/
theorem conditioned_pool (k : ℕ) (hk : 2 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (f : Finset U → C) (B V : Finset U) (hB : #B ≤ k - 2) (hV : k + 5 ≤ #V) :
    2 ^ k * #((powersetCard k V).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k V).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image f)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  set L : Finset U → ℕ := fun Y => 2 ^ (m + 2) - #(Y.powerset.image f) with hL
  set j := m + 2 - #B with hj
  have hj2 : 2 ≤ j := by omega
  have key : ∀ G : Finset U → ℕ,
      ∑ W ∈ (powersetCard m V).filter (fun W => B ⊆ W),
        ∑ a ∈ V \ W, ∑ b ∈ (V \ W).erase a, G (insert a (insert b W)) =
      ∑ Y ∈ (powersetCard (m + 2) V).filter (fun Y => B ⊆ Y), j * (j - 1) * G Y := by
    intro G
    have hP := presentation_sum_pool V m
      (fun Y a b => if a ∉ B ∧ b ∉ B ∧ B ⊆ Y then G Y else 0)
    rw [sum_filter, sum_filter]
    convert hP using 1
    · apply sum_congr rfl; intro W _
      by_cases hBW : B ⊆ W
      · simp only [hBW, if_true]
        apply sum_congr rfl; intro a ha; apply sum_congr rfl; intro b hb
        rw [mem_sdiff] at ha; rw [mem_erase, mem_sdiff] at hb
        have haB : a ∉ B := fun h => ha.2 (hBW h)
        have hbB : b ∉ B := fun h => hb.2.2 (hBW h)
        have : B ⊆ insert a (insert b W) := hBW.trans (by intro x hx; simp [hx])
        simp [haB, hbB, this]
      · simp only [hBW, if_false]
        symm; apply sum_eq_zero; intro a ha; apply sum_eq_zero; intro b hb
        rw [mem_sdiff] at ha; rw [mem_erase, mem_sdiff] at hb
        rw [if_neg]
        rintro ⟨haB, hbB, hBY⟩
        apply hBW; intro x hx
        have := hBY hx
        simp only [mem_insert] at this
        rcases this with rfl | rfl | h
        · exact absurd hx haB
        · exact absurd hx hbB
        · exact h
    · apply sum_congr rfl; intro Y hY
      rw [mem_powersetCard] at hY
      by_cases hBY : B ⊆ Y
      · simp only [hBY, and_true, if_true]
        rw [pair_count B Y (G Y)]
        have : #(Y \ B) = j := by rw [card_sdiff_of_subset hBY, hY.2]
        rw [this]
      · simp only [hBY, and_false, if_false]
        symm; apply sum_eq_zero; intro a _; apply sum_eq_zero; intro b _; simp
  have hW : ∀ W ∈ (powersetCard m V).filter (fun W => B ⊆ W),
      2 ^ (m + 2) * (#(V \ W) * (#(V \ W) - 1)) ≤
        32 * ∑ a ∈ V \ W, ∑ b ∈ (V \ W).erase a, L (insert a (insert b W)) := by
    intro W hWm
    rw [mem_filter, mem_powersetCard] at hWm
    have hv : #(V \ W) = #V - m := by
      rw [card_sdiff_of_subset hWm.1.1, hWm.1.2]
    have h := core_bound f W (V \ W) sdiff_disjoint (by rw [hC, hWm.1.2, pow_add]; ring)
      (by rw [hv]; omega)
    rw [hC] at h; exact h
  have hcnt : ∀ W ∈ (powersetCard m V).filter (fun W => B ⊆ W),
      #(V \ W) * (#(V \ W) - 1) =
        ∑ a ∈ V \ W, ∑ b ∈ (V \ W).erase a, (fun _ => (1 : ℕ)) (insert a (insert b W)) := by
    intro W _
    rw [sum_congr rfl (g := fun _ => #(V \ W) - 1)]
    · rw [sum_const, smul_eq_mul]
    · intro a ha; rw [sum_const, card_erase_of_mem ha, smul_eq_mul, mul_one]
  have hsum := sum_le_sum hW
  rw [← mul_sum, ← mul_sum, key L] at hsum
  rw [sum_congr rfl hcnt, key (fun _ => 1)] at hsum
  simp only [mul_one, sum_const, smul_eq_mul] at hsum
  rw [← mul_sum] at hsum
  have hpos : 0 < j * (j - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc j * (j - 1) * (2 ^ (m + 2) * #((powersetCard (m + 2) V).filter (fun Y => B ⊆ Y)))
      = 2 ^ (m + 2) * (#((powersetCard (m + 2) V).filter (fun Y => B ⊆ Y)) * (j * (j - 1))) := by
        ring
    _ ≤ 32 * (j * (j - 1) * ∑ Y ∈ (powersetCard (m + 2) V).filter (fun Y => B ⊆ Y), L Y) := hsum
    _ = _ := by ring

end

end E624R10A

namespace Erdos624

theorem conditioned_alon_pool {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 2 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (f : Finset U → C) (B V : Finset U) (hB : #B ≤ k - 2) (hV : k + 5 ≤ #V) :
    2 ^ k * #((powersetCard k V).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k V).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image f)) := by
  exact E624R10A.conditioned_pool k hk hC f B V hB hV

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 2 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (f : Finset U → C) (B V : Finset U) (hB : #B ≤ k - 2) (hV : k + 5 ≤ #V) :
    2 ^ k * #((powersetCard k V).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k V).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image f)) :=
  Erdos624.conditioned_alon_pool k hk hC f B V hB hV
