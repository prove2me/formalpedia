-- Prove2me | solution 1 for Erdos624.robust_alon_sum
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-23T19:27:36.687748+00:00
-- url     : https://prove2.me/submissions/b3993a85-01de-4589-a962-d71481949717

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R4
open Finset

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Double counting of presentations `Y = W ∪ {a, b}`. -/
lemma presentation_sum (m : ℕ) (F : Finset U → ℕ) :
    ∑ W ∈ powersetCard m (univ : Finset U), ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a,
      F (insert a (insert b W)) =
    ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), (m + 2) * (m + 1) * F Y := by
  classical
  set R1 : Finset (Finset U × U × U) := univ.filter
    (fun p => #p.1 = m ∧ p.2.1 ∉ p.1 ∧ p.2.2 ∉ p.1 ∧ p.2.2 ≠ p.2.1) with hR1
  set R2 : Finset (Finset U × U × U) := univ.filter
    (fun p => #p.1 = m + 2 ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1 ∧ p.2.2 ≠ p.2.1) with hR2
  have e1 : ∑ W ∈ powersetCard m (univ : Finset U), ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a,
      F (insert a (insert b W)) = ∑ p ∈ R1, F (insert p.2.1 (insert p.2.2 p.1)) := by
    rw [Finset.sum_finset_product (r := R1) (s := powersetCard m univ)
      (t := fun W => ((univ \ W) ×ˢ univ).filter (fun ab => ab.2 ∈ (univ \ W).erase ab.1))]
    · apply Finset.sum_congr rfl
      intro W _
      rw [Finset.sum_finset_product (r := ((univ \ W) ×ˢ univ).filter
        (fun ab => ab.2 ∈ (univ \ W).erase ab.1)) (s := univ \ W)
        (t := fun a => (univ \ W).erase a)]
      intro p; simp only [mem_filter, mem_product, mem_univ, and_true]
    · intro p
      simp only [hR1, mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ,
        mem_product, mem_sdiff, mem_erase, and_true]
      tauto
  have e2 : ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), (m + 2) * (m + 1) * F Y =
      ∑ p ∈ R2, F p.1 := by
    rw [Finset.sum_finset_product (r := R2) (s := powersetCard (m + 2) univ)
      (t := fun Y => (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))]
    · apply Finset.sum_congr rfl
      intro Y hY
      rw [mem_powersetCard] at hY
      rw [Finset.sum_finset_product (r := (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))
        (s := Y) (t := fun a => Y.erase a)]
      · rw [Finset.sum_congr rfl (g := fun _ => (m + 1) * F Y)]
        · rw [sum_const, hY.2, smul_eq_mul]; ring
        · intro a ha
          show ∑ _b ∈ Y.erase a, F Y = _
          rw [sum_const, card_erase_of_mem ha, hY.2, smul_eq_mul]; simp
      · intro p; simp only [mem_filter, mem_product, mem_univ, and_true]
    · intro p
      simp only [hR2, mem_filter, mem_univ, true_and, mem_powersetCard, subset_univ,
        mem_product, mem_erase, and_true]
      tauto
  rw [e1, e2]
  apply Finset.sum_nbij' (fun p => (insert p.2.1 (insert p.2.2 p.1), p.2.1, p.2.2))
    (fun p => ((p.1.erase p.2.1).erase p.2.2, p.2.1, p.2.2))
  · rintro ⟨W, a, b⟩ h
    simp only [hR1, hR2, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, mem_insert_self _ _, mem_insert_of_mem (mem_insert_self _ _), h4⟩
    rw [card_insert_of_notMem, card_insert_of_notMem h3, h1]
    simp [h2, Ne.symm h4]
  · rintro ⟨Y, a, b⟩ h
    simp only [hR1, hR2, mem_filter, mem_univ, true_and] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨?_, by simp, by simp, h4⟩
    rw [card_erase_of_mem (mem_erase.2 ⟨h4, h3⟩), card_erase_of_mem h2, h1]; rfl
  · rintro ⟨W, a, b⟩ h
    simp only [hR1, mem_filter, mem_univ, true_and] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [Prod.mk.injEq, and_true]
    ext x; simp only [mem_erase, mem_insert]
    constructor
    · rintro ⟨hb, ha, (rfl | rfl | hx)⟩ <;> tauto
    · intro hx; refine ⟨?_, ?_, Or.inr (Or.inr hx)⟩ <;> rintro rfl <;> contradiction
  · rintro ⟨Y, a, b⟩ h
    simp only [hR2, mem_filter, mem_univ, true_and] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
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


/-- Palette of the one-point extensions by `a` over `W`. -/
def pal (f : Finset U → U) (W : Finset U) (a : U) : Finset U :=
  W.powerset.image (fun A => f (insert a A))

lemma pal_card_le (f : Finset U → U) (W : Finset U) (a : U) : #(pal f W a) ≤ 2 ^ #W := by
  unfold pal; exact (card_image_le).trans (card_powerset W).le

/-- Local loss bound (B.3): on `Y = W ∪ {a,b}` the image has at most
`2·2^|W| + |S_a| + |S_b| - |S_a ∩ S_b|` points. -/
lemma local_bound (f : Finset U → U) (W : Finset U) (a b : U) (hab : a ≠ b)
    (ha : a ∉ W) (hb : b ∉ W) :
    #((insert a (insert b W)).powerset.image f) + #(pal f W a ∩ pal f W b) ≤
      2 * 2 ^ #W + #(pal f W a) + #(pal f W b) := by
  have hsub : (insert a (insert b W)).powerset.image f ⊆
      (W.powerset.image f ∪ W.powerset.image (fun A => f (insert a (insert b A)))) ∪
        (pal f W a ∪ pal f W b) := by
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
    (fun A => f (insert a (insert b A)))) (pal f W a ∪ pal f W b)
  have h3 := card_union_le (W.powerset.image f) (W.powerset.image
    (fun A => f (insert a (insert b A))))
  have h4 : #(W.powerset.image f) ≤ 2 ^ #W := (card_image_le).trans (card_powerset W).le
  have h5 : #(W.powerset.image (fun A => f (insert a (insert b A)))) ≤ 2 ^ #W :=
    (card_image_le).trans (card_powerset W).le
  have h6 := card_union_add_card_inter (pal f W a) (pal f W b)
  omega


lemma card_inter_eq_sum (S T : Finset U) :
    (#(S ∩ T) : ℤ) = ∑ u, (if u ∈ S then (1 : ℤ) else 0) * (if u ∈ T then 1 else 0) := by
  have : S ∩ T = univ.filter (fun u => u ∈ S ∧ u ∈ T) := by ext u; simp
  rw [this, card_filter]; push_cast
  apply sum_congr rfl; intro u _
  by_cases h1 : u ∈ S <;> by_cases h2 : u ∈ T <;> simp [h1, h2]

lemma card_eq_sum (S : Finset U) : (#S : ℤ) = ∑ u, (if u ∈ S then (1 : ℤ) else 0) := by
  have : S = univ.filter (fun u => u ∈ S) := by ext u; simp
  conv_lhs => rw [this]
  rw [card_filter]; push_cast; rfl

/-- Per-`W` averaged bound (B.4) in counting form, for `|U| = 4·2^|W|` and `v = |U \ W| ≥ 7`. -/
lemma perW_bound (f : Finset U → U) (W : Finset U)
    (hU : Fintype.card U = 4 * 2 ^ #W) (hv : 7 ≤ #(univ \ W)) :
    Fintype.card U * (#(univ \ W) * (#(univ \ W) - 1)) ≤
      32 * ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a,
        (Fintype.card U - #((insert a (insert b W)).powerset.image f)) := by
  set V := univ \ W with hV
  set q : ℕ := 2 ^ #W with hq
  set n := Fintype.card U with hn
  set v := #V with hvdef
  have hq0 : 0 < q := by positivity
  -- integer versions
  set s : U → ℤ := fun a => #(pal f W a) with hs
  set I : U → U → ℤ := fun a b => #(pal f W a ∩ pal f W b) with hI
  set x : U → U → ℤ := fun u a => if u ∈ pal f W a then 1 else 0 with hx
  set σ : ℤ := ∑ a ∈ V, s a with hσ
  set E2 : ℤ := ∑ u, (∑ a ∈ V, x u a) ^ 2 with hE2
  -- termwise bound
  have hterm : ∀ a ∈ V, ∀ b ∈ V.erase a,
      (2 * (q : ℤ) - s a - s b + I a b) ≤
        ((n - #((insert a (insert b W)).powerset.image f) : ℕ) : ℤ) := by
    intro a ha b hb
    rw [hV, mem_sdiff] at ha
    rw [mem_erase, hV, mem_sdiff] at hb
    have hl := local_bound f W a b (Ne.symm hb.1) ha.2 hb.2.2
    have hle : #((insert a (insert b W)).powerset.image f) ≤ n := by
      rw [hn]; exact card_le_univ _
    rw [Nat.cast_sub hle]
    simp only [hs, hI]
    have : (n : ℤ) = 4 * q := by exact_mod_cast hU
    omega
  have hsum_le := sum_le_sum (fun a ha => sum_le_sum (hterm a ha))
  -- evaluate the left side
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
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← hσ, ← hvdef]
    ring
  -- Cauchy–Schwarz
  have hCS : σ ^ 2 ≤ (n : ℤ) * E2 := by
    rw [hσ2, hE2, hn, ← Finset.card_univ]
    exact sq_sum_le_card_mul_sum_sq
  have hsq : ∀ a, s a ≤ q := fun a => by simp only [hs]; exact_mod_cast pal_card_le f W a
  have hσle : σ ≤ (q : ℤ) * v := by
    calc σ ≤ ∑ a ∈ V, (q : ℤ) := sum_le_sum (fun a _ => hsq a)
      _ = q * v := by rw [sum_const, nsmul_eq_mul, hvdef]; ring
  have hnq : (n : ℤ) = 4 * q := by exact_mod_cast hU
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


lemma seven_le (m : ℕ) (hm : 1 ≤ m) : m + 7 ≤ 2 ^ (m + 2) := by
  have := @Nat.lt_two_pow_self m
  rw [pow_add]; omega

/-- Robust Alon, counting form, for a general finite type with `2^k` elements. -/
theorem robust_alon_sum_gen (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (f : Finset U → U) :
    2 ^ k * #(powersetCard k (univ : Finset U)) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset U), (2 ^ k - #(Y.powerset.image f)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  set F : Finset U → ℕ := fun Y => 2 ^ (m + 2) - #(Y.powerset.image f) with hF
  have hP := presentation_sum m F
  have hP1 := presentation_sum (U := U) m (fun _ => 1)
  have hcount : ∀ W ∈ powersetCard m (univ : Finset U),
      ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a, (fun _ => (1 : ℕ)) (insert a (insert b W)) =
        #(univ \ W) * (#(univ \ W) - 1) := by
    intro W _
    rw [sum_congr rfl (g := fun _ => #(univ \ W) - 1)]
    · rw [sum_const, smul_eq_mul]
    · intro a ha; rw [sum_const, card_erase_of_mem ha, smul_eq_mul, mul_one]
  have hW : ∀ W ∈ powersetCard m (univ : Finset U),
      2 ^ (m + 2) * (#(univ \ W) * (#(univ \ W) - 1)) ≤
        32 * ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a, F (insert a (insert b W)) := by
    intro W hWm
    rw [mem_powersetCard] at hWm
    have hv : #(univ \ W) = 2 ^ (m + 2) - m := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hU, hWm.2]
    have h := perW_bound f W (by rw [hU, hWm.2, pow_add]; ring)
      (by rw [hv]; have := seven_le m hm; omega)
    rw [hU] at h; exact h
  have hsum := sum_le_sum hW
  rw [← mul_sum, ← mul_sum, hP] at hsum
  rw [sum_congr rfl hcount] at hP1
  rw [hP1] at hsum
  simp only [mul_one] at hsum
  rw [← mul_sum, sum_const, smul_eq_mul] at hsum
  have hpos : 0 < (m + 2) * (m + 1) := by positivity
  have : (m + 2) * (m + 1) * (2 ^ (m + 2) * #(powersetCard (m + 2) (univ : Finset U))) ≤
      (m + 2) * (m + 1) * (32 * ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), F Y) := by
    calc _ = 2 ^ (m + 2) * (#(powersetCard (m + 2) (univ : Finset U)) * ((m + 2) * (m + 1))) := by ring
      _ ≤ 32 * ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), (m + 2) * (m + 1) * F Y := by
          linarith [hsum]
      _ = _ := by rw [← mul_sum]; ring
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Robust Alon, probability form: at least a `1/64` fraction of `k`-sets lose `≥ n/64` points. -/
theorem robust_alon_count_gen (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (f : Finset U → U) :
    #(powersetCard k (univ : Finset U)) ≤
      64 * #((powersetCard k (univ : Finset U)).filter
        (fun Y => 2 ^ k ≤ 64 * (2 ^ k - #(Y.powerset.image f)))) := by
  set K := powersetCard k (univ : Finset U)
  set L : Finset U → ℕ := fun Y => 2 ^ k - #(Y.powerset.image f)
  set G := K.filter (fun Y => 2 ^ k ≤ 64 * L Y)
  have h1 := robust_alon_sum_gen k hk hU f
  have hsplit := sum_filter_add_sum_filter_not K (fun Y => 2 ^ k ≤ 64 * L Y) L
  have hG : ∑ Y ∈ G, L Y ≤ ∑ Y ∈ G, 2 ^ k := sum_le_sum (fun Y _ => Nat.sub_le _ _)
  have hB : ∑ Y ∈ K.filter (fun Y => ¬ 2 ^ k ≤ 64 * L Y), 64 * L Y ≤
      ∑ Y ∈ K.filter (fun Y => ¬ 2 ^ k ≤ 64 * L Y), 2 ^ k :=
    sum_le_sum (fun Y hY => by rw [mem_filter] at hY; omega)
  rw [← mul_sum, sum_const, smul_eq_mul] at hB
  rw [sum_const, smul_eq_mul] at hG
  have hcK : #(K.filter (fun Y => ¬ 2 ^ k ≤ 64 * L Y)) ≤ #K := card_filter_le _ _
  have hpos : 0 < 2 ^ k := by positivity
  have : 2 ^ k * #K ≤ 2 ^ k * (64 * #G) := by
    have e : ∑ Y ∈ K, L Y = ∑ Y ∈ G, L Y + ∑ Y ∈ K.filter (fun Y => ¬ 2 ^ k ≤ 64 * L Y), L Y :=
      hsplit.symm
    have h1' : 2 ^ k * #K ≤ 32 * ∑ Y ∈ K, L Y := h1
    nlinarith [Nat.mul_le_mul_left (2 ^ k) hcK]
  exact Nat.le_of_mul_le_mul_left this hpos

end E624R4

namespace E624R4
open Finset Erdos624

lemma ees_mono {n m m' : ℕ} (h : ExistsEventuallySurjective n m) (hm : m ≤ m') :
    ExistsEventuallySurjective n m' := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, fun Y hY => hf Y (le_trans hm hY)⟩

lemma ees_succ {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (n + 1) := by
  refine ⟨fun _ => ⟨0, hn⟩, ?_⟩
  intro Y hY
  have : #Y ≤ n := by simpa using Finset.card_le_univ Y
  omega

lemma H_spec {n : ℕ} (hn : 0 < n) : ExistsEventuallySurjective n (H n) := by
  unfold H; rw [if_pos hn]
  exact Nat.sInf_mem (s := {m : ℕ | ExistsEventuallySurjective n m}) ⟨n + 1, ees_succ hn⟩

lemma H_le {n m : ℕ} (hn : 0 < n) (h : ExistsEventuallySurjective n m) : H n ≤ m := by
  unfold H; rw [if_pos hn]; exact Nat.sInf_le h

theorem lt_H_iff {n m : ℕ} (hn : 0 < n) : m < H n ↔ ¬ ExistsEventuallySurjective n m := by
  constructor
  · intro h1 h2; have := H_le hn h2; omega
  · intro h1; by_contra h2; push Not at h2; exact h1 (ees_mono (H_spec hn) h2)

theorem robust_alon_sum (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    2 ^ k * #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset (Fin (2 ^ k))),
        (2 ^ k - #(Y.powerset.image f)) :=
  robust_alon_sum_gen k hk (by simp) f

theorem robust_alon_count (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      64 * #((powersetCard k (univ : Finset (Fin (2 ^ k)))).filter
        (fun Y => 2 ^ k ≤ 64 * (2 ^ k - #(Y.powerset.image f)))) :=
  robust_alon_count_gen k hk (by simp) f

theorem lt_H_two_pow (k : ℕ) (hk : 3 ≤ k) : k < H (2 ^ k) := by
  rw [lt_H_iff (by positivity)]
  rintro ⟨f, hf⟩
  have h := robust_alon_sum k hk f
  have hK : 0 < #(powersetCard k (univ : Finset (Fin (2 ^ k)))) := by
    rw [card_powersetCard, card_univ, Fintype.card_fin]
    exact Nat.choose_pos (Nat.lt_two_pow_self).le
  have hz : ∑ Y ∈ powersetCard k (univ : Finset (Fin (2 ^ k))),
      (2 ^ k - #(Y.powerset.image f)) = 0 := by
    apply sum_eq_zero; intro Y hY
    rw [mem_powersetCard] at hY
    rw [hf Y hY.2.ge, card_univ, Fintype.card_fin, Nat.sub_self]
  rw [hz] at h
  have : 0 < 2 ^ k * #(powersetCard k (univ : Finset (Fin (2 ^ k)))) := by positivity
  omega

end E624R4


namespace Erdos624

theorem robust_alon_sum (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    2 ^ k * #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset (Fin (2 ^ k))),
        (2 ^ k - #(Y.powerset.image f)) :=
  E624R4.robust_alon_sum k hk f

end Erdos624

open Erdos624 in
theorem solution (k : ℕ) (hk : 3 ≤ k) (f : Finset (Fin (2 ^ k)) → Fin (2 ^ k)) :
    2 ^ k * #(powersetCard k (univ : Finset (Fin (2 ^ k)))) ≤
      32 * ∑ Y ∈ powersetCard k (univ : Finset (Fin (2 ^ k))),
        (2 ^ k - #(Y.powerset.image f)) :=
  Erdos624.robust_alon_sum k hk f

#print axioms solution
