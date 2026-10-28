-- Prove2me | solution 1 for Erdos624.resilient_packing_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:34:35.014816+00:00
-- url     : https://prove2.me/submissions/425a07b0-5417-4ea7-a76f-c8c46db286b9

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

namespace E624R11
open Finset

section
variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

/-- Swap a sum over pivots `y ∈ V` and `k`-sets through `y`. -/
lemma pivot_swap (V : Finset U) (k : ℕ) (F : Finset U → ℕ) :
    ∑ y ∈ V, ∑ Y ∈ (powersetCard k V).filter (fun Y => {y} ⊆ Y), F Y =
      ∑ Y ∈ powersetCard k V, k * F Y := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro Y hY
  rw [mem_powersetCard] at hY
  rw [← sum_filter]
  have : V.filter (fun y => {y} ⊆ Y) = Y := by
    ext y; simp only [mem_filter, singleton_subset_iff]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hY.1 h, h⟩
  rw [this, sum_const, hY.2, smul_eq_mul]

theorem parity_palette (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (V : Finset U) (hV : k + 5 ≤ #V) (ε : ℕ) :
    2 ^ k * #(powersetCard k V) ≤
      32 * ∑ Y ∈ powersetCard k V,
        (2 ^ k - #((Y.powerset.filter (fun A => #A % 2 = ε)).biUnion
          (fun A => ({g0 A, g1 A} : Finset C)))) := by
  by_cases hε : 2 ≤ ε
  · have hempty : ∀ Y : Finset U, (Y.powerset.filter (fun A => #A % 2 = ε)) = ∅ := by
      intro Y; apply filter_false_of_mem; intro A _; omega
    simp only [hempty, biUnion_empty, card_empty, Nat.sub_zero, sum_const, smul_eq_mul]
    nlinarith [Nat.zero_le (2 ^ k * #(powersetCard k V))]
  push Not at hε
  set J : Finset U → Finset C := fun Y => (Y.powerset.filter (fun A => #A % 2 = ε)).biUnion
          (fun A => ({g0 A, g1 A} : Finset C)) with hJ
  -- per pivot
  have hpiv : ∀ y ∈ V, 2 ^ k * #((powersetCard k V).filter (fun Y => {y} ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k V).filter (fun Y => {y} ⊆ Y), (2 ^ k - #(J Y)) := by
    intro y hy
    set ψ : Finset U → Finset U := fun A => if #A % 2 = ε then A else insert y A with hψ
    set f : Finset U → C := fun A => (if y ∈ A then g1 else g0) (ψ (A.erase y)) with hf
    have h := E624R10A.conditioned_pool k (by omega) hC f {y} V (by simp; omega) hV
    refine h.trans (Nat.mul_le_mul_left _ (sum_le_sum ?_))
    intro Y hY
    rw [mem_filter, singleton_subset_iff] at hY
    apply Nat.sub_le_sub_left
    apply card_le_card
    intro c hc
    simp only [hJ, mem_biUnion, mem_filter, mem_powerset] at hc
    obtain ⟨A, ⟨hA, hpar⟩, hcA⟩ := hc
    have hψA : ψ (A.erase y) = A := by
      simp only [hψ]
      by_cases hyA : y ∈ A
      · have hc1 : #(A.erase y) + 1 = #A := card_erase_add_one hyA
        rw [if_neg (by omega), insert_erase hyA]
      · rw [erase_eq_of_notMem hyA, if_pos hpar]
    have hyE : y ∉ A.erase y := notMem_erase _ _
    simp only [mem_insert, mem_singleton] at hcA
    rcases hcA with rfl | rfl
    · refine mem_image.2 ⟨A.erase y, mem_powerset.2 ((erase_subset _ _).trans hA), ?_⟩
      simp only [hf, if_neg hyE, erase_eq_of_notMem hyE, hψA]
    · refine mem_image.2 ⟨insert y (A.erase y),
        mem_powerset.2 (insert_subset hY.2 ((erase_subset _ _).trans hA)), ?_⟩
      simp only [hf, if_pos (mem_insert_self _ _), erase_insert hyE, hψA]
  have hsum := sum_le_sum hpiv
  rw [← mul_sum, ← mul_sum] at hsum
  have e1 := pivot_swap V k (fun _ => 1)
  have e2 := pivot_swap V k (fun Y => 2 ^ k - #(J Y))
  simp only [sum_const, smul_eq_mul, mul_one] at e1
  rw [e1, e2, ← mul_sum] at hsum
  have hk0 : 0 < k := by omega
  apply Nat.le_of_mul_le_mul_left _ hk0
  calc k * (2 ^ k * #(powersetCard k V)) = 2 ^ k * (#(powersetCard k V) * k) := by ring
    _ ≤ 32 * (k * ∑ Y ∈ powersetCard k V, (2 ^ k - #(J Y))) := hsum
    _ = _ := by ring

theorem proper_odd_palette (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (V : Finset U) (hV : k + 5 ≤ #V) :
    2 ^ k * #(powersetCard k V) ≤
      32 * ∑ Y ∈ powersetCard k V,
        (2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y ∧ #A % 2 = 1)).biUnion
          (fun A => ({g0 A, g1 A} : Finset C)))) := by
  refine (parity_palette k hk hC g0 g1 V hV 1).trans (Nat.mul_le_mul_left _ (sum_le_sum ?_))
  intro Y _
  apply Nat.sub_le_sub_left
  apply card_le_card
  apply biUnion_subset_biUnion_of_subset_left
  intro A; simp only [mem_filter]; exact fun h => ⟨h.1, h.2.2⟩

end
end E624R11

namespace E624R11
open Finset

section
variable {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

lemma zmod2_eq_one_of_ne_zero : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide

/-- Face inequality (14). -/
theorem face_bound (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (S : Finset C)
    (hS : ∀ u ∈ S, u ∉ ({g0 ∅, g1 ∅} : Finset C))
    (R : C → Finset U) (w : C → U → ZMod 2)
    (hw : ∀ u ∈ S, ∀ A ⊆ V \ R u, 0 < #A → #A < k → u ∈ ({g0 A, g1 A} : Finset C) →
      (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) → ∑ x ∈ A, w u x = 1)
    (Y : Finset U) (hYV : Y ⊆ V) (hY : #Y = k) :
    Fintype.card C - #((Y.powerset.filter (fun A => A ≠ Y ∧ #A % 2 = 1)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C))) ≤
      (Fintype.card C - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)))) + (Fintype.card C - #S) +
      #(S.filter (fun u => ¬ Disjoint Y (R u ∪ (V \ R u).filter (fun x => w u x = 0)))) := by
  set Jo := (Y.powerset.filter (fun A => A ≠ Y ∧ #A % 2 = 1)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)) with hJo
  set Jp := (Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)) with hJp
  set M := S.filter (fun u => ¬ Disjoint Y (R u ∪ (V \ R u).filter (fun x => w u x = 0))) with hM
  have key : univ \ Jo ⊆ ((univ \ Jp) ∪ (univ \ S)) ∪ M := by
    intro u hu
    rw [mem_sdiff] at hu
    by_contra hcon
    simp only [mem_union, mem_sdiff, mem_univ, true_and, not_or, not_not, hM, mem_filter] at hcon
    obtain ⟨⟨huJp, huS⟩, hmeet⟩ := hcon
    have hdisj : Disjoint Y (R u ∪ (V \ R u).filter (fun x => w u x = 0)) := by
      by_contra h; exact hmeet ⟨huS, h⟩
    set P := Y.powerset.filter (fun A => A ≠ Y ∧ u ∈ ({g0 A, g1 A} : Finset C)) with hP
    have hne : P.Nonempty := by
      rw [hJp, mem_biUnion] at huJp
      obtain ⟨A, hA, huA⟩ := huJp
      rw [mem_filter] at hA
      exact ⟨A, by rw [hP, mem_filter]; exact ⟨hA.1, hA.2, huA⟩⟩
    obtain ⟨A, hAP, hmin⟩ := P.exists_min_image card hne
    rw [hP, mem_filter, mem_powerset] at hAP
    obtain ⟨hAY, hAne, huA⟩ := hAP
    have hA0 : 0 < #A := by
      rw [card_pos]; by_contra h; rw [not_nonempty_iff_eq_empty] at h
      subst h; exact hS u huS huA
    have hAk : #A < k := by
      rw [← hY]; exact card_lt_card (lt_of_le_of_ne hAY hAne)
    have hAV : A ⊆ V \ R u := by
      intro x hx
      rw [mem_sdiff]
      refine ⟨hYV (hAY hx), fun hxR => ?_⟩
      exact disjoint_left.1 hdisj (hAY hx) (mem_union_left _ hxR)
    have hAmin : ∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C) := by
      intro B hB huB
      have hBP : B ∈ P := by
        rw [hP, mem_filter, mem_powerset]
        refine ⟨hB.1.trans hAY, ?_, huB⟩
        rintro rfl
        exact absurd (card_lt_card hB) (by have := card_le_card hAY; omega)
      have := hmin B hBP
      have := card_lt_card hB
      omega
    have hsum := hw u huS A hAV hA0 hAk huA hAmin
    have hone : ∀ x ∈ A, w u x = 1 := by
      intro x hx
      apply zmod2_eq_one_of_ne_zero
      intro h0
      apply disjoint_left.1 hdisj (hAY hx)
      apply mem_union_right
      rw [mem_filter]; exact ⟨hAV hx, h0⟩
    rw [sum_congr rfl hone, sum_const, nsmul_eq_mul, mul_one] at hsum
    have hodd : #A % 2 = 1 := Fin.mk_eq_one.mp hsum
    apply hu.2
    rw [hJo, mem_biUnion]
    exact ⟨A, by rw [mem_filter, mem_powerset]; exact ⟨hAY, hAne, hodd⟩, huA⟩
  have h1 := card_le_card key
  have h2 := card_union_le ((univ \ Jp) ∪ (univ \ S)) M
  have h3 := card_union_le (univ \ Jp) (univ \ S)
  simp only [card_univ_sdiff] at h1 h3
  omega

end

section
variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

lemma card_through (V : Finset U) (x : U) (hx : x ∈ V) (j : ℕ) :
    #((powersetCard (j + 1) V).filter (fun Y => x ∈ Y)) = (#V - 1).choose j := by
  rw [← card_erase_of_mem hx, ← card_powersetCard]
  symm
  apply card_nbij' (fun Y => insert x Y) (fun Y => Y.erase x)
  · intro Y hY
    simp only [mem_coe, mem_powersetCard] at hY
    simp only [mem_coe, mem_filter, mem_powersetCard, mem_insert_self, and_true]
    refine ⟨insert_subset hx (hY.1.trans (erase_subset _ _)), ?_⟩
    rw [card_insert_of_notMem (fun h => by simpa using hY.1 h), hY.2]
  · intro Y hY
    simp only [mem_coe, mem_filter, mem_powersetCard] at hY
    simp only [mem_coe, mem_powersetCard]
    refine ⟨erase_subset_erase _ hY.1.1, ?_⟩
    rw [card_erase_of_mem hY.2, hY.1.2]; rfl
  · intro Y hY
    simp only [mem_coe, mem_powersetCard] at hY
    exact erase_insert (fun h => by simpa using hY.1 h)
  · intro Y hY
    simp only [mem_coe, mem_filter] at hY
    exact insert_erase hY.2

lemma card_meeting (V E : Finset U) (k : ℕ) (hk : 1 ≤ k) :
    #V * #((powersetCard k V).filter (fun Y => ¬ Disjoint Y E)) ≤
      #E * (k * #(powersetCard k V)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsub : (powersetCard (j + 1) V).filter (fun Y => ¬ Disjoint Y E) ⊆
      (E ∩ V).biUnion (fun x => (powersetCard (j + 1) V).filter (fun Y => x ∈ Y)) := by
    intro Y hY
    rw [mem_filter, mem_powersetCard] at hY
    rw [not_disjoint_iff] at hY
    obtain ⟨⟨hYV, _⟩, x, hxY, hxE⟩ := hY
    rw [mem_biUnion]
    exact ⟨x, mem_inter.2 ⟨hxE, hYV hxY⟩, mem_filter.2 ⟨mem_powersetCard.2 ⟨hYV, by omega⟩, hxY⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  rw [sum_congr rfl (fun x hx => card_through V x (mem_inter.1 hx).2 j), sum_const,
    smul_eq_mul] at h1
  have hEV : #(E ∩ V) ≤ #E := card_le_card inter_subset_left
  rcases Nat.eq_zero_or_pos #V with h0 | hpos
  · rw [h0]; simp
  obtain ⟨M, hM⟩ : ∃ M, #V = M + 1 := ⟨#V - 1, by omega⟩
  have hch : #V * (#V - 1).choose j = (j + 1) * #(powersetCard (j + 1) V) := by
    rw [card_powersetCard, hM, Nat.add_sub_cancel, Nat.add_one_mul_choose_eq]; ring
  calc #V * #((powersetCard (j + 1) V).filter (fun Y => ¬ Disjoint Y E))
      ≤ #V * (#(E ∩ V) * (#V - 1).choose j) := Nat.mul_le_mul_left _ h1
    _ ≤ #V * (#E * (#V - 1).choose j) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hEV)
    _ = #E * (#V * (#V - 1).choose j) := by ring
    _ = _ := by rw [hch]

/-- Certificate inequality (13). -/
theorem certificate_ineq (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (g0 g1 : Finset U → C) (V : Finset U) (hV : k + 5 ≤ #V) (S : Finset C)
    (hS : ∀ u ∈ S, u ∉ ({g0 ∅, g1 ∅} : Finset C))
    (R : C → Finset U) (w : C → U → ZMod 2)
    (hw : ∀ u ∈ S, ∀ A ⊆ V \ R u, 0 < #A → #A < k → u ∈ ({g0 A, g1 A} : Finset C) →
      (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) → ∑ x ∈ A, w u x = 1) :
    2 ^ k * #V * #(powersetCard k V) ≤
      32 * #V * ∑ Y ∈ powersetCard k V, (2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)))) +
      32 * #V * (2 ^ k - #S) * #(powersetCard k V) +
      32 * k * #(powersetCard k V) *
        ∑ u ∈ S, (#(R u) + #((V \ R u).filter (fun x => w u x = 0))) := by
  set K := #(powersetCard k V) with hK
  set N := #V with hN
  set E : C → Finset U := fun u => R u ∪ (V \ R u).filter (fun x => w u x = 0) with hE
  set Qo : Finset U → ℕ := fun Y => 2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y ∧ #A % 2 = 1)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C))) with hQo
  set Dp : Finset U → ℕ := fun Y => 2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C))) with hDp
  have h11 : 2 ^ k * K ≤ 32 * ∑ Y ∈ powersetCard k V, Qo Y := proper_odd_palette k hk hC g0 g1 V hV
  have h14 : ∀ Y ∈ powersetCard k V, Qo Y ≤ Dp Y + (2 ^ k - #S) +
      #(S.filter (fun u => ¬ Disjoint Y (E u))) := by
    intro Y hY
    rw [mem_powersetCard] at hY
    have := face_bound k g0 g1 V S hS R w hw Y hY.1 hY.2
    rw [hC] at this; exact this
  have hsum14 := sum_le_sum h14
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at hsum14
  have hswap : ∑ Y ∈ powersetCard k V, #(S.filter (fun u => ¬ Disjoint Y (E u))) =
      ∑ u ∈ S, #((powersetCard k V).filter (fun Y => ¬ Disjoint Y (E u))) := by
    simp only [card_filter]; rw [sum_comm]
  have hmeet : ∀ u ∈ S, N * #((powersetCard k V).filter (fun Y => ¬ Disjoint Y (E u))) ≤
      (#(R u) + #((V \ R u).filter (fun x => w u x = 0))) * (k * K) := by
    intro u _
    exact (card_meeting V (E u) k (by omega)).trans
      (Nat.mul_le_mul_right _ (card_union_le _ _))
  have hm2 := sum_le_sum hmeet
  rw [← mul_sum, ← sum_mul] at hm2
  rw [hswap] at hsum14
  have hNpos : 0 < N := by omega
  calc 2 ^ k * N * K = N * (2 ^ k * K) := by ring
    _ ≤ N * (32 * ∑ Y ∈ powersetCard k V, Qo Y) := Nat.mul_le_mul_left _ h11
    _ ≤ N * (32 * (∑ Y ∈ powersetCard k V, Dp Y + K * (2 ^ k - #S) +
          ∑ u ∈ S, #((powersetCard k V).filter (fun Y => ¬ Disjoint Y (E u))))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsum14)
    _ = 32 * N * ∑ Y ∈ powersetCard k V, Dp Y + 32 * N * (2 ^ k - #S) * K +
          32 * (N * ∑ u ∈ S, #((powersetCard k V).filter (fun Y => ¬ Disjoint Y (E u)))) := by ring
    _ ≤ 32 * N * ∑ Y ∈ powersetCard k V, Dp Y + 32 * N * (2 ^ k - #S) * K +
          32 * ((∑ u ∈ S, (#(R u) + #((V \ R u).filter (fun x => w u x = 0)))) * (k * K)) := by
        gcongr
    _ = _ := by ring

end
end E624R11

namespace E624R11PH

open Finset

lemma ph_choose_succ_ge_aux (e : ℕ) : ∀ q : ℕ, e + 1 ≤ (q + 1 + e).choose (q + 1)
  | 0 => by simp [Nat.choose_one_right]
  | q + 1 => by
    have ih := ph_choose_succ_ge_aux e q
    have h : (q + 1 + 1 + e).choose (q + 1 + 1)
        = (q + 1 + e).choose (q + 1) + (q + 1 + e).choose (q + 1 + 1) := by
      rw [show q + 1 + 1 + e = (q + 1 + e) + 1 by omega, Nat.choose_succ_succ]
    omega

/-- `C(d, q+1) + q ≥ d`. -/
lemma ph_choose_add_ge (d q : ℕ) : d ≤ d.choose (q + 1) + q := by
  rcases Nat.lt_or_ge q d with h | h
  · obtain ⟨e, rfl⟩ : ∃ e, d = q + 1 + e := ⟨d - (q + 1), by omega⟩
    have := ph_choose_succ_ge_aux e q
    omega
  · omega

/-- **Joint proper-hole packing lemma** (capacity `q`). Let `L : Finset U → Finset C` be a list
system with `|L A| ≤ q`, `V` a pool of size `N`, and `a ≥ 1` with `N > (k-1) C((q+1)a, q+1)`.
If `(q+1)a` distinct colours `u i` have proper holes `T i ⊆ V` (no input `A ⊆ T i` with
`|A| < k` carries `u i`) with `a |T i| ≥ N`, then some `k`-subset `Y ⊆ V` misses one of these
colours: `u i ∉ ⋃_{A ⊆ Y} L A`. -/
theorem proper_hole_packing {U C : Type*} [DecidableEq U] [DecidableEq C]
    (L : Finset U → Finset C) (q k a : ℕ) (V : Finset U)
    (hq : ∀ A, (L A).card ≤ q) (ha : 1 ≤ a)
    (hN : (k - 1) * ((q + 1) * a).choose (q + 1) < V.card)
    (u : Fin ((q + 1) * a) → C) (hu : Function.Injective u)
    (T : Fin ((q + 1) * a) → Finset U) (hTV : ∀ i, T i ⊆ V)
    (hhole : ∀ i, ∀ A ⊆ T i, A.card < k → u i ∉ L A)
    (hsize : ∀ i, V.card ≤ a * (T i).card) :
    ∃ Y ∈ V.powersetCard k, ∃ i, u i ∉ Y.powerset.biUnion L := by
  classical
  set N := V.card
  -- degrees
  set d : U → ℕ := fun x => (univ.filter (fun i : Fin ((q + 1) * a) => x ∈ T i)).card
  -- Step A: Σ_x d_x = Σ_i |T i|
  have hA : ∑ x ∈ V, d x = ∑ i : Fin ((q + 1) * a), (T i).card := by
    simp only [d, Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.card_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hTV i h, h⟩⟩
  -- Step B: (q+1) N ≤ Σ_i |T i|
  have hB : (q + 1) * N ≤ ∑ i : Fin ((q + 1) * a), (T i).card := by
    have h1 : ∑ _i : Fin ((q + 1) * a), N ≤ ∑ i : Fin ((q + 1) * a), a * (T i).card :=
      Finset.sum_le_sum (fun i _ => hsize i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      at h1
    have h2 : a * ((q + 1) * N) ≤ a * ∑ i : Fin ((q + 1) * a), (T i).card := by
      calc a * ((q + 1) * N) = (q + 1) * a * N := by ring
        _ ≤ _ := h1
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  -- Step C: Σ_x C(d_x, q+1) ≥ N
  have hC : N ≤ ∑ x ∈ V, (d x).choose (q + 1) := by
    have h1 : ∑ x ∈ V, d x ≤ ∑ x ∈ V, ((d x).choose (q + 1) + q) :=
      Finset.sum_le_sum (fun x _ => ph_choose_add_ge (d x) q)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h1
    have : (q + 1) * N = N + q * N := by ring
    have h3 : V.card * q = q * N := by simp [N, mul_comm]
    omega
  -- Step D: double count
  have hD : ∑ x ∈ V, (d x).choose (q + 1)
      = ∑ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
          (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card := by
    have hx : ∀ x, (d x).choose (q + 1)
        = ∑ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
            if (∀ i ∈ I, x ∈ T i) then 1 else 0 := by
      intro x
      rw [Finset.sum_boole, Nat.cast_id, ← Finset.card_powersetCard]
      congr 1
      ext I
      simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_iff,
        Finset.mem_univ, true_and, implies_true]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    simp only [hx]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    rw [Finset.card_filter]
  -- Step E: some (q+1)-intersection has ≥ k points
  have hE : ∃ I ∈ (univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1),
      k ≤ (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card := by
    by_contra hcon
    push Not at hcon
    have h1 := Finset.sum_le_card_nsmul ((univ : Finset (Fin ((q + 1) * a))).powersetCard (q + 1))
      (fun I => (V.filter (fun x => ∀ i ∈ I, x ∈ T i)).card) (k - 1)
      (fun I hI => by have := hcon I hI; omega)
    rw [smul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h1
    have : ((q + 1) * a).choose (q + 1) * (k - 1) = (k - 1) * ((q + 1) * a).choose (q + 1) :=
      mul_comm _ _
    omega
  obtain ⟨I, hI, hIk⟩ := hE
  obtain ⟨Y, hYsub, hYcard⟩ := Finset.exists_subset_card_eq hIk
  have hYV : Y ⊆ V := hYsub.trans (Finset.filter_subset _ _)
  have hYT : ∀ i ∈ I, Y ⊆ T i := by
    intro i hi x hx
    exact (Finset.mem_filter.1 (hYsub hx)).2 i hi
  refine ⟨Y, Finset.mem_powersetCard.2 ⟨hYV, hYcard⟩, ?_⟩
  by_contra hall
  push Not at hall
  -- every colour u i (i ∈ I) sits on the top input Y
  have htop : I.image u ⊆ L Y := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hc
    obtain ⟨A, hA, huA⟩ := Finset.mem_biUnion.1 (hall i)
    rw [Finset.mem_powerset] at hA
    by_cases hAY : A = Y
    · exact hAY ▸ huA
    · exfalso
      have hss : A ⊂ Y := Finset.ssubset_iff_subset_ne.2 ⟨hA, hAY⟩
      have hcard : A.card < k := hYcard ▸ Finset.card_lt_card hss
      exact hhole i A (hA.trans (hYT i hi)) hcard huA
  have h1 := Finset.card_le_card htop
  rw [Finset.card_image_of_injective _ hu, (Finset.mem_powersetCard.1 hI).2] at h1
  have := hq Y
  omega


end E624R11PH

namespace E624R11
open Finset

section
variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

lemma choose_three_bound (k : ℕ) :
    (k - 1) * (3 * (256 * k)).choose 3 * 6 ≤ 452984832 * k ^ 4 := by
  have h1 : (3 * (256 * k)).descFactorial 3 = Nat.factorial 3 * (3 * (256 * k)).choose 3 :=
    Nat.descFactorial_eq_factorial_mul_choose _ _
  have h2 : (3 * (256 * k)).descFactorial 3 ≤ (3 * (256 * k)) ^ 3 := Nat.descFactorial_le_pow _ _
  have h3 : Nat.factorial 3 = 6 := rfl
  rw [h3] at h1
  have h4 : (3 * (256 * k)).choose 3 * 6 ≤ 452984832 * k ^ 3 := by
    have : (3 * (256 * k)) ^ 3 = 452984832 * k ^ 3 := by ring
    omega
  calc (k - 1) * (3 * (256 * k)).choose 3 * 6 = (k - 1) * ((3 * (256 * k)).choose 3 * 6) := by ring
    _ ≤ k * (452984832 * k ^ 3) := Nat.mul_le_mul (Nat.sub_le _ _) h4
    _ = 452984832 * k ^ 4 := by ring

lemma zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

theorem resilience (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C) (V : Finset U)
    (hV : 2 ^ 28 * k ^ 4 ≤ #V)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1 := by
  classical
  set N := #V with hN
  set n := 2 ^ k with hn
  set L : Finset U → Finset C := fun A => ({g0 A, g1 A} : Finset C) with hL
  have hL2 : ∀ A, #(L A) ≤ 2 := fun A => by
    simp only [hL]; exact (card_insert_le _ _).trans (by simp)
  have hk4 : k ≤ k ^ 4 := by
    calc k = k ^ 1 := (pow_one k).symm
      _ ≤ k ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hNbig : 98304 * k + 512 ≤ N := by
    have : (2 : ℕ) ^ 28 = 268435456 := by norm_num
    rw [this] at hV; nlinarith
  have hNn : N ≤ n := by have := card_le_univ V; rw [hU] at this; exact this
  set res : C → Prop := fun u => u ∉ L ∅ ∧
      ∀ R ⊆ V, 256 * k * #R ≤ N → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ L A → (∀ B ⊂ A, u ∉ L B) → ∑ x ∈ A, w x = 1 with hres
  set H := univ.filter res with hH
  refine ⟨H, ?_, fun u hu => (mem_filter.1 hu).2⟩
  -- big proper holes
  set a := 256 * k with ha
  set Bc := univ.filter (fun u : C => ∃ T : Finset U, T ⊆ V ∧ (∀ A ⊆ T, #A < k → u ∉ L A) ∧
      N ≤ a * #T) with hBc
  have hBcard : #Bc < 3 * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨Bs, hBs, hcard⟩ := exists_subset_card_eq hcon
    have hc' : (2 + 1) * a = #Bs := by rw [hcard]
    let u : Fin ((2 + 1) * a) → C := fun i => (Bs.equivFin.symm (Fin.cast hc' i)).1
    have hu : Function.Injective u := by
      intro i j hij
      have := Subtype.ext hij
      simpa using this
    have hmem : ∀ i, u i ∈ Bc := fun i => hBs (Bs.equivFin.symm (Fin.cast hc' i)).2
    have hex : ∀ i, ∃ T : Finset U, T ⊆ V ∧ (∀ A ⊆ T, #A < k → u i ∉ L A) ∧ N ≤ a * #T :=
      fun i => (mem_filter.1 (hmem i)).2
    choose T hT using hex
    have hNp : (k - 1) * ((2 + 1) * a).choose (2 + 1) < V.card := by
      have := choose_three_bound k
      have h5 : (2 : ℕ) ^ 28 = 268435456 := by norm_num
      rw [h5] at hV
      show (k - 1) * (3 * (256 * k)).choose 3 < N
      have hk0 : 0 < k ^ 4 := by positivity
      omega
    obtain ⟨Y, hY, i, hi⟩ := E624R11PH.proper_hole_packing L 2 k a V hL2 (by omega) hNp u hu T
      (fun i => (hT i).1) (fun i => (hT i).2.1) (fun i => (hT i).2.2)
    obtain ⟨A, hAY, huA⟩ := hcov Y hY (u i)
    exact hi (mem_biUnion.2 ⟨A, mem_powerset.2 hAY, huA⟩)
  -- the set S
  set S := univ.filter (fun u : C => u ∉ L ∅ ∧ u ∉ H ∧ u ∉ Bc) with hS
  have hex : ∀ u ∈ S, ∃ R : Finset U, ∃ w : U → ZMod 2, R ⊆ V ∧ 256 * k * #R ≤ N ∧
      ∀ A ⊆ V \ R, 0 < #A → #A < k → u ∈ L A → (∀ B ⊂ A, u ∉ L B) → ∑ x ∈ A, w x = 1 := by
    intro u hu
    rw [hS, mem_filter] at hu
    obtain ⟨_, hL0, hnH, _⟩ := hu
    have : ¬ res u := fun h => hnH (mem_filter.2 ⟨mem_univ _, h⟩)
    simp only [hres, not_and, not_forall, not_not] at this
    obtain ⟨R, hRV, hRs, w, hw⟩ := this hL0
    exact ⟨R, w, hRV, hRs, hw⟩
  choose! R w hRw using hex
  set T : C → Finset U := fun u => (V \ R u).filter (fun x => w u x = 0) with hT
  have hThole : ∀ u ∈ S, ∀ A ⊆ T u, #A < k → u ∉ L A := by
    intro u hu A hA hAk huA
    have hL0 : u ∉ L ∅ := (mem_filter.1 hu).2.1
    set P := A.powerset.filter (fun B => u ∈ L B) with hP
    have hne : P.Nonempty := ⟨A, mem_filter.2 ⟨mem_powerset_self _, huA⟩⟩
    obtain ⟨A', hA'P, hmin⟩ := P.exists_min_image card hne
    rw [hP, mem_filter, mem_powerset] at hA'P
    have hA'T : A' ⊆ T u := hA'P.1.trans hA
    have hA'V : A' ⊆ V \ R u := hA'T.trans (filter_subset _ _)
    have hpos : 0 < #A' := by
      rw [card_pos]; by_contra h; rw [not_nonempty_iff_eq_empty] at h
      subst h; exact hL0 hA'P.2
    have hlt : #A' < k := lt_of_le_of_lt (card_le_card hA'P.1) hAk
    have hminl : ∀ B ⊂ A', u ∉ L B := by
      intro B hB huB
      have := hmin B (mem_filter.2 ⟨mem_powerset.2 (hB.1.trans hA'P.1), huB⟩)
      have := card_lt_card hB; omega
    have hsum := (hRw u hu).2.2 A' hA'V hpos hlt hA'P.2 hminl
    have hzero : ∀ x ∈ A', w u x = 0 := fun x hx => (mem_filter.1 (hA'T hx)).2
    rw [sum_congr rfl hzero, sum_const_zero] at hsum
    exact zmod2_zero_ne_one hsum
  have hTsmall : ∀ u ∈ S, a * #(T u) < N := by
    intro u hu
    have hnB : u ∉ Bc := (mem_filter.1 hu).2.2.2
    by_contra hcon; push Not at hcon
    exact hnB (mem_filter.2 ⟨mem_univ _, T u, filter_subset _ _ |>.trans sdiff_subset,
      hThole u hu, hcon⟩)
  have hRT : ∀ u ∈ S, 128 * k * (#(R u) + #(T u)) ≤ N := by
    intro u hu
    have h1 := (hRw u hu).2.1
    have h2 := hTsmall u hu
    rw [ha] at h2
    have e1 : 256 * k * #(R u) = 2 * (128 * k * #(R u)) := by ring
    have e2 : 256 * k * #(T u) = 2 * (128 * k * #(T u)) := by ring
    have e3 : 128 * k * (#(R u) + #(T u)) = 128 * k * #(R u) + 128 * k * #(T u) := by ring
    omega
  have hRTsum : 128 * k * ∑ u ∈ S, (#(R u) + #(T u)) ≤ #S * N := by
    rw [mul_sum]
    calc ∑ u ∈ S, 128 * k * (#(R u) + #(T u)) ≤ ∑ u ∈ S, N := sum_le_sum hRT
      _ = #S * N := by rw [sum_const, smul_eq_mul]
  -- (13)
  have hV5 : k + 5 ≤ N := by omega
  have h13 := certificate_ineq k hk hC g0 g1 V hV5 S (fun u hu => (mem_filter.1 hu).2.1) R w
    (fun u hu => (hRw u hu).2.2)
  -- proper deficits are at most 2
  have hD : ∀ Y ∈ powersetCard k V, n - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
      (fun A => ({g0 A, g1 A} : Finset C))) ≤ 2 := by
    intro Y hY
    set Jp := (Y.powerset.filter (fun A => A ≠ Y)).biUnion (fun A => ({g0 A, g1 A} : Finset C))
    have hsub : univ \ Jp ⊆ L Y := by
      intro u hu
      rw [mem_sdiff] at hu
      obtain ⟨A, hAY, huA⟩ := hcov Y hY u
      by_cases hAeq : A = Y
      · rw [← hAeq]; exact huA
      · exact absurd (mem_biUnion.2 ⟨A, mem_filter.2 ⟨mem_powerset.2 hAY, hAeq⟩, huA⟩) hu.2
    have := (card_le_card hsub).trans (hL2 Y)
    rw [card_univ_sdiff, hC] at this
    exact this
  have hDsum := sum_le_sum hD
  rw [sum_const, smul_eq_mul] at hDsum
  set K := #(powersetCard k V) with hK
  set s := #S with hs
  have hKpos : 0 < K := by
    rw [hK, card_powersetCard]; exact Nat.choose_pos (by omega)
  have hsn : s ≤ n := by have := card_le_univ S; rw [hC] at this; exact this
  obtain ⟨t, ht⟩ : ∃ t, n = s + t := ⟨n - s, by omega⟩
  set SD := ∑ Y ∈ powersetCard k V, (2 ^ k - #((Y.powerset.filter (fun A => A ≠ Y)).biUnion
        (fun A => ({g0 A, g1 A} : Finset C)))) with hSD
  set SRT := ∑ u ∈ S, (#(R u) + #(T u)) with hSRT
  have hnt : n - s = t := by omega
  rw [← hn, hnt] at h13
  have key : (4 * (s + t)) * (N * K) ≤ (256 + 128 * t + s) * (N * K) := by
    have e1 : 32 * N * SD ≤ 32 * N * (K * 2) := Nat.mul_le_mul_left _ hDsum
    have e3 : K * (128 * k * SRT) ≤ K * (s * N) := Nat.mul_le_mul_left _ hRTsum
    have h13' : (s + t) * N * K ≤ 32 * N * SD + 32 * N * t * K + 32 * k * K * SRT := by
      rw [← ht]; exact h13
    nlinarith
  have h4 : 4 * (s + t) ≤ 256 + 128 * t + s :=
    Nat.le_of_mul_le_mul_right key (Nat.mul_pos (by omega) hKpos)
  -- counting the complement of S
  have hcover : (univ : Finset C) ⊆ ((S ∪ L ∅) ∪ H) ∪ Bc := by
    intro u _
    by_cases h1 : u ∈ L ∅
    · simp [h1]
    by_cases h2 : u ∈ H
    · simp [h2]
    by_cases h3 : u ∈ Bc
    · simp [h3]
    simp [hS, h1, h2, h3]
  have hc := card_le_card hcover
  rw [card_univ, hC] at hc
  have hc2 : #(((S ∪ L ∅) ∪ H) ∪ Bc) ≤ #S + #(L ∅) + #H + #Bc := by
    have := card_union_le ((S ∪ L ∅) ∪ H) Bc
    have := card_union_le (S ∪ L ∅) H
    have := card_union_le S (L ∅)
    omega
  have hL0 := hL2 ∅
  have : n ≤ s + 2 + #H + #Bc := by
    have := hc.trans hc2; omega
  omega

end
end E624R11

namespace E624R12A
open Finset

lemma pow_bound (k : ℕ) (hk : 51 ≤ k) : 2 ^ 28 * k ^ 4 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
      have hm3 : 0 ≤ m ^ 3 := Nat.zero_le _
      nlinarith [Nat.mul_le_mul_right (m ^ 3) hm, Nat.mul_le_mul_right (m ^ 2) hm,
        Nat.mul_le_mul_right m hm]
    calc 2 ^ 28 * (m + 1) ^ 4 ≤ 2 ^ 28 * (2 * m ^ 4) := Nat.mul_le_mul_left _ h1
      _ = 2 * (2 ^ 28 * m ^ 4) := by ring
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (m + 1) := by ring

section
variable {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]

theorem full_domain (k : ℕ) (hk : 51 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C)
    (hcov : ∀ Y : Finset U, #Y = k → ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ R : Finset U, 256 * k * #R ≤ 2 ^ k → ¬ ∃ w : U → ZMod 2, ∀ A : Finset U, Disjoint A R →
        0 < #A → #A < k → u ∈ ({g0 A, g1 A} : Finset C) →
          (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) → ∑ x ∈ A, w x = 1 := by
  have hV : 2 ^ 28 * k ^ 4 ≤ #(univ : Finset U) := by rw [card_univ, hU]; exact pow_bound k hk
  obtain ⟨H, hH, hres⟩ := E624R11.resilience k (by omega) hU hC g0 g1 univ hV
    (fun Y hY u => hcov Y (mem_powersetCard.1 hY).2 u)
  refine ⟨H, hH, fun u hu => ⟨(hres u hu).1, fun R hR => ?_⟩⟩
  rw [card_univ, hU] at *
  rintro ⟨w, hw⟩
  apply (hres u hu).2 R (subset_univ _) hR
  refine ⟨w, fun A hA => hw A ?_⟩
  rw [disjoint_left]; intro x hx hxR
  exact (mem_sdiff.1 (hA hx)).2 hxR

theorem localization (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C) (V : Finset U)
    (hV : #V = 2 ^ 28 * k ^ 4)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ R ⊆ V, #R ≤ 2 ^ 20 * k ^ 3 → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1 := by
  obtain ⟨H, hH, hres⟩ := E624R11.resilience k hk hU hC g0 g1 V hV.ge hcov
  refine ⟨H, hH, fun u hu => ⟨(hres u hu).1, fun R hRV hR => (hres u hu).2 R hRV ?_⟩⟩
  rw [hV]
  calc 256 * k * #R ≤ 256 * k * (2 ^ 20 * k ^ 3) := Nat.mul_le_mul_left _ hR
    _ = 2 ^ 28 * k ^ 4 := by ring

lemma zmod2_cases : ∀ z : ZMod 2, z ≠ 1 → z = 0 := by decide

theorem packing (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (u : C)
    (hres : ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1)
    (w : U → ZMod 2) :
    ∃ P : Finset (Finset U),
      (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
        (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      #V < 256 * k * (k - 1) * #P := by
  classical
  set E := V.powerset.filter (fun A => 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
        (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) with hE
  set Fam := E.powerset.filter (fun P => ∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) with hFam
  have hne : Fam.Nonempty := ⟨∅, by simp [hFam]⟩
  obtain ⟨P, hPF, hmax⟩ := Fam.exists_max_image card hne
  rw [hFam, mem_filter, mem_powerset] at hPF
  obtain ⟨hPE, hPd⟩ := hPF
  have hmemP : ∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
      (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0 := by
    intro A hA
    have := hPE hA
    rw [hE, mem_filter, mem_powerset] at this
    exact ⟨this.1, this.2⟩
  refine ⟨P, hmemP, hPd, ?_⟩
  set R := P.biUnion id with hR
  have hRV : R ⊆ V := by
    intro x hx; rw [hR, mem_biUnion] at hx
    obtain ⟨A, hA, hxA⟩ := hx; exact (hmemP A hA).1 hxA
  have hRcard : #R ≤ (k - 1) * #P := by
    calc #R ≤ ∑ A ∈ P, #(id A) := card_biUnion_le
      _ ≤ ∑ A ∈ P, (k - 1) := sum_le_sum (fun A hA => by
          have := (hmemP A hA).2.2.1; simp only [id]; omega)
      _ = (k - 1) * #P := by rw [sum_const, smul_eq_mul, mul_comm]
  have hcert : ∃ w' : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
      u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
        ∑ x ∈ A, w' x = 1 := by
    refine ⟨w, fun A hA h0 hk' hu hmin => ?_⟩
    by_contra hne1
    have hz := zmod2_cases _ hne1
    have hAV : A ⊆ V := hA.trans sdiff_subset
    have hAE : A ∈ E := by rw [hE, mem_filter, mem_powerset]; exact ⟨hAV, h0, hk', hu, hmin, hz⟩
    have hAR : Disjoint A R := by
      rw [disjoint_left]; intro x hx hxR; exact (mem_sdiff.1 (hA hx)).2 hxR
    have hAnP : A ∉ P := by
      intro hAP
      obtain ⟨x, hx⟩ := card_pos.1 h0
      exact disjoint_left.1 hAR hx (mem_biUnion.2 ⟨A, hAP, hx⟩)
    have hins : insert A P ∈ Fam := by
      rw [hFam, mem_filter, mem_powerset]
      refine ⟨insert_subset hAE hPE, ?_⟩
      intro X hX Y hY hXY
      rw [mem_insert] at hX hY
      rcases hX with rfl | hX <;> rcases hY with rfl | hY
      · exact absurd rfl hXY
      · rw [disjoint_left]; intro x hx hxY
        exact disjoint_left.1 hAR hx (mem_biUnion.2 ⟨Y, hY, hxY⟩)
      · rw [disjoint_left]; intro x hxX hx
        exact disjoint_left.1 hAR hx (mem_biUnion.2 ⟨X, hX, hxX⟩)
      · exact hPd X hX Y hY hXY
    have := hmax _ hins
    rw [card_insert_of_notMem hAnP] at this
    omega
  have hlt : ¬ 256 * k * #R ≤ #V := fun h => hres R hRV h hcert
  push Not at hlt
  calc #V < 256 * k * #R := hlt
    _ ≤ 256 * k * ((k - 1) * #P) := Nat.mul_le_mul_left _ hRcard
    _ = 256 * k * (k - 1) * #P := by ring

theorem resilience_packing (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C) (V : Finset U)
    (hV : 2 ^ 28 * k ^ 4 ≤ #V)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ w : U → ZMod 2, ∃ P : Finset (Finset U),
        (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
          (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
        (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
        #V < 256 * k * (k - 1) * #P := by
  obtain ⟨H, hH, hres⟩ := E624R11.resilience k hk hU hC g0 g1 V hV hcov
  exact ⟨H, hH, fun u hu => ⟨(hres u hu).1, fun w => packing k g0 g1 V u (hres u hu).2 w⟩⟩

end
end E624R12A

namespace Erdos624

theorem resilient_packing_bound {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (u : C)
    (hres : ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1)
    (w : U → ZMod 2) :
    ∃ P : Finset (Finset U),
      (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
        (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      #V < 256 * k * (k - 1) * #P := by
  exact E624R12A.packing k g0 g1 V u hres w

end Erdos624

open Finset

theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (u : C)
    (hres : ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1)
    (w : U → ZMod 2) :
    ∃ P : Finset (Finset U),
      (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
        (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      #V < 256 * k * (k - 1) * #P :=
  Erdos624.resilient_packing_bound k g0 g1 V u hres w
