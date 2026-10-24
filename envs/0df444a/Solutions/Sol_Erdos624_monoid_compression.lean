-- Prove2me | solution 1 for Erdos624.monoid_compression
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-24T03:33:41.302109+00:00
-- url     : https://prove2.me/submissions/fead7d37-94da-4384-9e0f-5ebd3a284d02

import Mathlib
import Definitions.Def_Erdos624_defs
open Finset


namespace E624R6
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


/-- Double counting of presentations `Y = W ∪ {a, b}`, with weights depending on `(Y, a, b)`. -/
lemma presentation_sum3 (m : ℕ) (F : Finset U → U → U → ℕ) :
    ∑ W ∈ powersetCard m (univ : Finset U), ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a,
      F (insert a (insert b W)) a b =
    ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), ∑ a ∈ Y, ∑ b ∈ Y.erase a, F Y a b := by
  classical
  set R1 : Finset (Finset U × U × U) := univ.filter
    (fun p => #p.1 = m ∧ p.2.1 ∉ p.1 ∧ p.2.2 ∉ p.1 ∧ p.2.2 ≠ p.2.1) with hR1
  set R2 : Finset (Finset U × U × U) := univ.filter
    (fun p => #p.1 = m + 2 ∧ p.2.1 ∈ p.1 ∧ p.2.2 ∈ p.1 ∧ p.2.2 ≠ p.2.1) with hR2
  have e1 : ∑ W ∈ powersetCard m (univ : Finset U), ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a,
      F (insert a (insert b W)) a b = ∑ p ∈ R1, F (insert p.2.1 (insert p.2.2 p.1)) p.2.1 p.2.2 := by
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
  have e2 : ∑ Y ∈ powersetCard (m + 2) (univ : Finset U), ∑ a ∈ Y, ∑ b ∈ Y.erase a, F Y a b =
      ∑ p ∈ R2, F p.1 p.2.1 p.2.2 := by
    rw [Finset.sum_finset_product (r := R2) (s := powersetCard (m + 2) univ)
      (t := fun Y => (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))]
    · apply Finset.sum_congr rfl
      intro Y hY
      rw [Finset.sum_finset_product (r := (Y ×ˢ univ).filter (fun ab => ab.2 ∈ Y.erase ab.1))
        (s := Y) (t := fun a => Y.erase a)]
      intro p; simp only [mem_filter, mem_product, mem_univ, and_true]
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

/-- **Conditioned Alon**, general finite type. -/
theorem conditioned_alon_gen (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (B : Finset U) (hB : #B ≤ k - 2) (g : Finset U → U) :
    2 ^ k * #((powersetCard k (univ : Finset U)).filter (fun Y => B ⊆ Y)) ≤
      32 * ∑ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => B ⊆ Y),
        (2 ^ k - #(Y.powerset.image g)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  set L : Finset U → ℕ := fun Y => 2 ^ (m + 2) - #(Y.powerset.image g) with hL
  set j := m + 2 - #B with hj
  have hj2 : 2 ≤ j := by omega
  -- weights
  have key : ∀ G : Finset U → ℕ,
      ∑ W ∈ (powersetCard m (univ : Finset U)).filter (fun W => B ⊆ W),
        ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a, G (insert a (insert b W)) =
      ∑ Y ∈ (powersetCard (m + 2) (univ : Finset U)).filter (fun Y => B ⊆ Y),
        j * (j - 1) * G Y := by
    intro G
    have hP := presentation_sum3 (U := U) m
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
  have hW : ∀ W ∈ (powersetCard m (univ : Finset U)).filter (fun W => B ⊆ W),
      2 ^ (m + 2) * (#(univ \ W) * (#(univ \ W) - 1)) ≤
        32 * ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a, L (insert a (insert b W)) := by
    intro W hWm
    rw [mem_filter, mem_powersetCard] at hWm
    have hv : #(univ \ W) = 2 ^ (m + 2) - m := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hU, hWm.1.2]
    have h := perW_bound g W (by rw [hU, hWm.1.2, pow_add]; ring)
      (by rw [hv]; have := seven_le m hm; omega)
    rw [hU] at h; exact h
  have hcnt : ∀ W ∈ (powersetCard m (univ : Finset U)).filter (fun W => B ⊆ W),
      #(univ \ W) * (#(univ \ W) - 1) =
        ∑ a ∈ univ \ W, ∑ b ∈ (univ \ W).erase a, (fun _ => (1 : ℕ)) (insert a (insert b W)) := by
    intro W _
    rw [sum_congr rfl (g := fun _ => #(univ \ W) - 1)]
    · rw [sum_const, smul_eq_mul]
    · intro a ha; rw [sum_const, card_erase_of_mem ha, smul_eq_mul, mul_one]
  have hsum := sum_le_sum hW
  rw [← mul_sum, ← mul_sum, key L] at hsum
  rw [sum_congr rfl hcnt, key (fun _ => 1)] at hsum
  simp only [mul_one, sum_const, smul_eq_mul] at hsum
  rw [← mul_sum] at hsum
  have hpos : 0 < j * (j - 1) := Nat.mul_pos (by omega) (by omega)
  apply Nat.le_of_mul_le_mul_left _ hpos
  calc j * (j - 1) * (2 ^ (m + 2) * #((powersetCard (m + 2) (univ : Finset U)).filter (fun Y => B ⊆ Y)))
      = 2 ^ (m + 2) * (#((powersetCard (m + 2) (univ : Finset U)).filter (fun Y => B ⊆ Y)) * (j * (j - 1))) := by ring
    _ ≤ 32 * (j * (j - 1) * ∑ Y ∈ (powersetCard (m + 2) (univ : Finset U)).filter (fun Y => B ⊆ Y), L Y) := hsum
    _ = _ := by ring

end E624R6

namespace E624R6
open Finset

section Monoid
variable {U : Type*} [Fintype U] [DecidableEq U]
variable {M : Type*} [CommMonoid M] [DecidableEq M]

/-- Distinct subset products of `v` over subsets of `S`. -/
def prodSet (v : U → M) (S : Finset U) : Finset M := S.powerset.image (fun A => ∏ x ∈ A, v x)

omit [Fintype U] in
lemma prodSet_card_le_pow (v : U → M) (S : Finset U) : #(prodSet v S) ≤ 2 ^ #S :=
  card_image_le.trans (card_powerset S).le

omit [Fintype U] in
lemma prodSet_union (v : U → M) (S T : Finset U) (h : Disjoint S T) :
    #(prodSet v (S ∪ T)) ≤ #(prodSet v S) * #(prodSet v T) := by
  have hsub : prodSet v (S ∪ T) ⊆ (prodSet v S ×ˢ prodSet v T).image (fun p => p.1 * p.2) := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hx
    rw [mem_powerset] at hA
    refine mem_image.2 ⟨(∏ x ∈ A ∩ S, v x, ∏ x ∈ A ∩ T, v x), ?_, ?_⟩
    · simp only [mem_product, prodSet]
      exact ⟨mem_image.2 ⟨A ∩ S, mem_powerset.2 inter_subset_right, rfl⟩,
        mem_image.2 ⟨A ∩ T, mem_powerset.2 inter_subset_right, rfl⟩⟩
    · dsimp only
      rw [← prod_union (Disjoint.mono inter_subset_right inter_subset_right h),
        ← inter_union_distrib_left, inter_eq_left.2 hA]
  calc #(prodSet v (S ∪ T)) ≤ #((prodSet v S ×ˢ prodSet v T).image (fun p => p.1 * p.2)) :=
        card_le_card hsub
    _ ≤ #(prodSet v S ×ˢ prodSet v T) := card_image_le
    _ = _ := card_product _ _

omit [Fintype U] in
/-- A collision inside `Bl` saves at least one product value. -/
lemma prodSet_collision (v : U → M) (Bl P Q : Finset U) (hP : P ⊆ Bl) (hQ : Q ⊆ Bl)
    (hne : P ≠ Q) (heq : ∏ x ∈ P, v x = ∏ x ∈ Q, v x) :
    #(prodSet v Bl) + 1 ≤ 2 ^ #Bl := by
  have hsub : prodSet v Bl ⊆ (Bl.powerset.erase P).image (fun A => ∏ x ∈ A, v x) := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.1 hx
    by_cases hAP : A = P
    · subst hAP
      exact mem_image.2 ⟨Q, mem_erase.2 ⟨Ne.symm hne, mem_powerset.2 hQ⟩, heq.symm⟩
    · exact mem_image.2 ⟨A, mem_erase.2 ⟨hAP, hA⟩, rfl⟩
  have h1 := (card_le_card hsub).trans card_image_le
  rw [card_erase_of_mem (mem_powerset.2 hP), card_powerset] at h1
  have : 0 < 2 ^ #Bl := by positivity
  omega

omit [Fintype U] in
lemma prodSet_biUnion {ι : Type*} [DecidableEq ι] (v : U → M) (Bk : ι → Finset U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) (s : Finset ι) :
    #(prodSet v (s.biUnion Bk)) ≤ ∏ i ∈ s, #(prodSet v (Bk i)) := by
  induction s using Finset.induction_on with
  | empty => simp [prodSet]
  | insert i s hi ih =>
    rw [biUnion_insert, prod_insert hi]
    have hd : Disjoint (Bk i) (s.biUnion Bk) := by
      rw [disjoint_biUnion_right]; intro j hj; exact hdisj i j (by rintro rfl; exact hi hj)
    exact (prodSet_union v _ _ hd).trans (Nat.mul_le_mul_left _ ih)

omit [Fintype U] in
/-- Image of `h(A) = ψ(∏ v)` on `P(Y)` is controlled by the products on a sub-support `S`. -/
lemma image_le_prodSet (v : U → M) (ψ : M → U) (S Y : Finset U) (hSY : S ⊆ Y) :
    #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤ #(prodSet v S) * 2 ^ (#Y - #S) := by
  have e : Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) = (prodSet v Y).image ψ := by
    rw [prodSet, image_image]; rfl
  have hY : Y = S ∪ (Y \ S) := (union_sdiff_of_subset hSY).symm
  calc #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤ #(prodSet v Y) := by
        rw [e]; exact card_image_le
    _ ≤ #(prodSet v S) * #(prodSet v (Y \ S)) := by
        conv_lhs => rw [hY]
        exact prodSet_union v S (Y \ S) disjoint_sdiff
    _ ≤ #(prodSet v S) * 2 ^ (#Y - #S) := by
        apply Nat.mul_le_mul_left
        have := prodSet_card_le_pow v (Y \ S)
        rwa [card_sdiff_of_subset hSY] at this

omit [Fintype U] in
/-- **Monoid compression (9).** -/
theorem monoid_compression_gen (t d : ℕ) (v : U → M) (ψ : M → U) (Bk P Q : Fin d → Finset U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) (hcard : ∀ i, #(Bk i) ≤ 2 * t)
    (hP : ∀ i, P i ⊆ Bk i) (hQ : ∀ i, Q i ⊆ Bk i) (hne : ∀ i, P i ≠ Q i)
    (heq : ∀ i, ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x)
    (Y : Finset U) (hY : (univ : Finset (Fin d)).biUnion Bk ⊆ Y) :
    (2 ^ (2 * t)) ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤
      (2 ^ (2 * t) - 1) ^ d * 2 ^ #Y := by
  set b := 2 ^ (2 * t) with hb
  set S := (univ : Finset (Fin d)).biUnion Bk with hS
  have hblock : ∀ i, b * #(prodSet v (Bk i)) ≤ (b - 1) * 2 ^ #(Bk i) := by
    intro i
    have h1 := prodSet_collision v (Bk i) (P i) (Q i) (hP i) (hQ i) (hne i) (heq i)
    have h2 : 2 ^ #(Bk i) ≤ b := Nat.pow_le_pow_right (by norm_num) (hcard i)
    have h3 : b * #(prodSet v (Bk i)) + b ≤ b * 2 ^ #(Bk i) := by
      have := Nat.mul_le_mul_left b h1; rw [mul_add, mul_one] at this; exact this
    rw [Nat.sub_mul, one_mul]
    have h4 : 2 ^ #(Bk i) ≤ b * 2 ^ #(Bk i) := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hcardS : #S = ∑ i, #(Bk i) := by
    rw [hS, card_biUnion]
    intro i _ j _ hij; exact hdisj i j hij
  have hprodS : b ^ d * #(prodSet v S) ≤ (b - 1) ^ d * 2 ^ #S := by
    calc b ^ d * #(prodSet v S) ≤ b ^ d * ∏ i, #(prodSet v (Bk i)) :=
          Nat.mul_le_mul_left _ (prodSet_biUnion v Bk hdisj univ)
      _ = ∏ i : Fin d, (b * #(prodSet v (Bk i))) := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin d, ((b - 1) * 2 ^ #(Bk i)) := prod_le_prod' (fun i _ => hblock i)
      _ = (b - 1) ^ d * 2 ^ #S := by
          rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, hcardS, prod_pow_eq_pow_sum]
  have hSY : #S ≤ #Y := card_le_card hY
  calc b ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)))
      ≤ b ^ d * (#(prodSet v S) * 2 ^ (#Y - #S)) :=
        Nat.mul_le_mul_left _ (image_le_prodSet v ψ S Y hY)
    _ = (b ^ d * #(prodSet v S)) * 2 ^ (#Y - #S) := by ring
    _ ≤ ((b - 1) ^ d * 2 ^ #S) * 2 ^ (#Y - #S) := Nat.mul_le_mul_right _ hprodS
    _ = (b - 1) ^ d * 2 ^ #Y := by rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hSY]

/-- **Collision blocks (7)–(8).** -/
theorem collision_blocks_gen [Fintype M] (t : ℕ) (v : U → M) : ∀ d : ℕ,
    Fintype.card M < (Fintype.card U - 2 * t * (d - 1)).choose t →
    ∃ Bk P Q : Fin d → Finset U, (∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) ∧
      ∀ i, #(Bk i) ≤ 2 * t ∧ P i ⊆ Bk i ∧ Q i ⊆ Bk i ∧ P i ≠ Q i ∧
        ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x
  | 0, _ => ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | d + 1, h7 => by
    have h7' : Fintype.card M < (Fintype.card U - 2 * t * (d - 1)).choose t :=
      lt_of_lt_of_le h7 (Nat.choose_le_choose _ (by
        have : 2 * t * (d - 1) ≤ 2 * t * d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        simp only [Nat.add_sub_cancel]; omega))
    obtain ⟨Bk, P, Q, hdisj, hprop⟩ := collision_blocks_gen t v d h7'
    set S := (univ : Finset (Fin d)).biUnion Bk with hS
    have hcS : #S ≤ 2 * t * d := by
      calc #S ≤ ∑ i, #(Bk i) := card_biUnion_le
        _ ≤ ∑ _i : Fin d, 2 * t := sum_le_sum (fun i _ => (hprop i).1)
        _ = 2 * t * d := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
    set R := (univ : Finset U) \ S with hR
    have hcR : Fintype.card U - 2 * t * d ≤ #R := by
      rw [hR, card_sdiff_of_subset (subset_univ _), card_univ]; omega
    have hlt : #(univ : Finset M) < #(powersetCard t R) := by
      rw [card_univ, card_powersetCard]
      refine lt_of_lt_of_le h7 (Nat.choose_le_choose _ ?_)
      simpa using hcR
    obtain ⟨P', hP', Q', hQ', hne', heq'⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun A => ∏ x ∈ A, v x) (fun _ _ => mem_coe.2 (mem_univ _))
    rw [mem_powersetCard] at hP' hQ'
    set Bl := P' ∪ Q' with hBl
    have hBlR : Bl ⊆ R := union_subset hP'.1 hQ'.1
    have hBlc : #Bl ≤ 2 * t := (card_union_le _ _).trans (by rw [hP'.2, hQ'.2]; omega)
    have hdisjBl : ∀ i, Disjoint (Bk i) Bl := by
      intro i
      have h1 : Bk i ⊆ S := subset_biUnion_of_mem Bk (mem_univ i)
      exact Disjoint.mono h1 hBlR (by rw [hR]; exact disjoint_sdiff)
    refine ⟨Fin.snoc (α := fun _ => Finset U) Bk Bl, Fin.snoc (α := fun _ => Finset U) P P',
      Fin.snoc (α := fun _ => Finset U) Q Q', ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact (hdisjBl j).symm
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp only [Fin.snoc_last, Fin.snoc_castSucc]; exact hdisjBl i
        | cast j =>
          simp only [Fin.snoc_castSucc]
          exact hdisj i j (fun h => hij (by rw [h]))
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact ⟨hBlc, subset_union_left, subset_union_right, hne', heq'⟩
      | cast i => simp only [Fin.snoc_castSucc]; exact hprop i

end Monoid
end E624R6

namespace E624R6
open Finset

section OneMap
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **General compression (3).** If `64 |I_h(Y)| ≤ n` on every completion of a core `S`,
then every second map has average joint loss `≥ n/64` on those completions. -/
theorem compression_surplus (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (S : Finset U) (hS : #S ≤ k - 2) (h g : Finset U → U)
    (hsmall : ∀ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y),
      64 * #(Y.powerset.image h) ≤ 2 ^ k) :
    2 ^ k * #((powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y)) ≤
      64 * ∑ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y),
        (2 ^ k - #(Y.powerset.image h ∪ Y.powerset.image g)) := by
  set KS := (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y)
  have hA : 2 ^ k * #KS ≤ 32 * ∑ Y ∈ KS, (2 ^ k - #(Y.powerset.image g)) :=
    conditioned_alon_gen k hk hU S hS g
  have hpt : ∀ Y ∈ KS, 64 * (2 ^ k - #(Y.powerset.image g)) ≤
      64 * (2 ^ k - #(Y.powerset.image h ∪ Y.powerset.image g)) + 2 ^ k := by
    intro Y hY
    have h1 := card_union_le (Y.powerset.image h) (Y.powerset.image g)
    have h2 := hsmall Y hY
    have h3 : #(Y.powerset.image h ∪ Y.powerset.image g) ≤ 2 ^ k := by
      rw [← hU]; exact card_le_univ _
    omega
  have hs := sum_le_sum hpt
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul] at hs
  have e : #KS * 2 ^ k = 2 ^ k * #KS := mul_comm _ _
  omega

variable {M : Type*} [CommMonoid M]

/-- **One structured map is enough (finite form).** -/
theorem one_structured_map_gen [Fintype M] (k t d : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (v : U → M) (ψ : M → U)
    (h7 : Fintype.card M < (2 ^ k - 2 * t * (d - 1)).choose t)
    (hd : 2 * t * d ≤ k - 2) (hb : 64 * (2 ^ (2 * t) - 1) ^ d ≤ (2 ^ (2 * t)) ^ d) :
    ∃ S : Finset U, #S ≤ k - 2 ∧ ∀ g : Finset U → U,
      2 ^ k * #((powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y)) ≤
        64 * ∑ Y ∈ (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y),
          (2 ^ k - #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∪ Y.powerset.image g)) := by
  classical
  rw [← hU] at h7
  obtain ⟨Bk, P, Q, hdisj, hprop⟩ := collision_blocks_gen t v d h7
  set S := (univ : Finset (Fin d)).biUnion Bk with hS
  have hcS : #S ≤ 2 * t * d := by
    calc #S ≤ ∑ i, #(Bk i) := card_biUnion_le
      _ ≤ ∑ _i : Fin d, 2 * t := sum_le_sum (fun i _ => (hprop i).1)
      _ = 2 * t * d := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; ring
  refine ⟨S, hcS.trans hd, fun g => compression_surplus k hk hU S (hcS.trans hd) _ g ?_⟩
  intro Y hY
  rw [mem_filter, mem_powersetCard] at hY
  have hc := monoid_compression_gen t d v ψ Bk P Q hdisj (fun i => (hprop i).1)
    (fun i => (hprop i).2.1) (fun i => (hprop i).2.2.1) (fun i => (hprop i).2.2.2.1)
    (fun i => (hprop i).2.2.2.2) Y hY.2
  rw [hY.1.2] at hc
  have hbpos : 0 < (2 ^ (2 * t)) ^ d := by positivity
  have : (2 ^ (2 * t)) ^ d * (64 * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)))) ≤
      (2 ^ (2 * t)) ^ d * 2 ^ k := by
    calc (2 ^ (2 * t)) ^ d * (64 * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))))
        = 64 * ((2 ^ (2 * t)) ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)))) := by ring
      _ ≤ 64 * ((2 ^ (2 * t) - 1) ^ d * 2 ^ k) := Nat.mul_le_mul_left _ hc
      _ = (64 * (2 ^ (2 * t) - 1) ^ d) * 2 ^ k := by ring
      _ ≤ (2 ^ (2 * t)) ^ d * 2 ^ k := Nat.mul_le_mul_right _ hb
  exact Nat.le_of_mul_le_mul_left this hbpos

/-- Common-hole form. -/
theorem one_structured_map_hole_gen [Fintype M] (k t d : ℕ) (hk : 3 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (v : U → M) (ψ : M → U)
    (h7 : Fintype.card M < (2 ^ k - 2 * t * (d - 1)).choose t)
    (hd : 2 * t * d ≤ k - 2) (hb : 64 * (2 ^ (2 * t) - 1) ^ d ≤ (2 ^ (2 * t)) ^ d)
    (g : Finset U → U) :
    ∃ Y : Finset U, #Y = k ∧ ∃ u : U,
      u ∉ Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∧ u ∉ Y.powerset.image g := by
  obtain ⟨S, hS, hsum⟩ := one_structured_map_gen k t d hk hU v ψ h7 hd hb
  have h := hsum g
  set KS := (powersetCard k (univ : Finset U)).filter (fun Y => S ⊆ Y)
  have hKS : 0 < #KS := by
    obtain ⟨Y, hSY, hY⟩ := Finset.exists_superset_card_eq (s := S) (n := k) (by omega)
      (by rw [hU]; exact (Nat.lt_two_pow_self).le)
    exact card_pos.2 ⟨Y, mem_filter.2 ⟨mem_powersetCard.2 ⟨subset_univ _, hY⟩, hSY⟩⟩
  have hpos : 0 < ∑ Y ∈ KS,
      (2 ^ k - #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∪ Y.powerset.image g)) := by
    have : 0 < 2 ^ k * #KS := by positivity
    omega
  obtain ⟨Y, hY, hYpos⟩ := exists_ne_zero_of_sum_ne_zero hpos.ne'
  rw [mem_filter, mem_powersetCard] at hY
  have hlt : #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∪ Y.powerset.image g) <
      #(univ : Finset U) := by rw [card_univ, hU]; omega
  obtain ⟨u, -, hu⟩ := exists_mem_notMem_of_card_lt_card hlt
  rw [mem_union, not_or] at hu
  exact ⟨Y, hY.1.2, u, hu⟩

end OneMap
end E624R6

namespace E624R6
open Finset

lemma bern_aux (x : ℕ) : ∀ m : ℕ, x ^ (m + 1) + m * x ^ m ≤ x * (x + 1) ^ m
  | 0 => by simp
  | m + 1 => by
    have ih := bern_aux x m
    have h : x * (x + 1) ^ (m + 1) = (x + 1) * (x * (x + 1) ^ m) := by ring
    rw [h]
    calc x ^ (m + 1 + 1) + (m + 1) * x ^ (m + 1)
        ≤ x ^ (m + 2) + x ^ (m + 1) + m * x ^ (m + 1) + m * x ^ m := by
          have : x ^ (m + 1 + 1) = x ^ (m + 2) := rfl
          nlinarith [Nat.zero_le (m * x ^ m)]
      _ = (x + 1) * (x ^ (m + 1) + m * x ^ m) := by ring
      _ ≤ (x + 1) * (x * (x + 1) ^ m) := Nat.mul_le_mul_left _ ih

/-- `2 (b-1)^b ≤ b^b` for `b ≥ 2`. -/
lemma two_mul_pow_le (b : ℕ) (hb : 2 ≤ b) : 2 * (b - 1) ^ b ≤ b ^ b := by
  obtain ⟨x, rfl⟩ : ∃ x, b = x + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have h := bern_aux x (x + 1)
  have hx : 1 ≤ x := by omega
  have : x * (2 * x ^ (x + 1)) ≤ x * (x + 1) ^ (x + 1) := by
    calc x * (2 * x ^ (x + 1)) = x ^ (x + 1) * x + x ^ (x + 1) * x := by ring
      _ ≤ x ^ (x + 1) * x + x ^ (x + 1) * (x + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
      _ = x ^ (x + 1 + 1) + (x + 1) * x ^ (x + 1) := by ring
      _ ≤ _ := h
  exact Nat.le_of_mul_le_mul_left this (by omega)

lemma sixtyfour_le (b : ℕ) (hb : 2 ≤ b) : 64 * (b - 1) ^ (6 * b) ≤ b ^ (6 * b) := by
  have h := two_mul_pow_le b hb
  have h6 := Nat.pow_le_pow_left h 6
  rw [mul_pow, ← pow_mul, ← pow_mul] at h6
  calc 64 * (b - 1) ^ (6 * b) = 2 ^ 6 * (b - 1) ^ (b * 6) := by ring_nf
    _ ≤ b ^ (b * 6) := h6
    _ = b ^ (6 * b) := by rw [mul_comm]

/-- `n^(t-1) < C(N, t)` when `n ≤ 4(N+1-t)` and `(4t)^t < n`. -/
lemma choose_big (n N t : ℕ) (ht : 1 ≤ t) (h1 : n ≤ 4 * (N + 1 - t)) (h2 : (4 * t) ^ t < n) :
    n ^ (t - 1) < N.choose t := by
  have hc : (N + 1 - t) ^ t ≤ t ^ t * N.choose t := by
    calc (N + 1 - t) ^ t ≤ N.descFactorial t := Nat.pow_sub_le_descFactorial N t
      _ = Nat.factorial t * N.choose t := Nat.descFactorial_eq_factorial_mul_choose N t
      _ ≤ t ^ t * N.choose t := Nat.mul_le_mul_right _ (Nat.factorial_le_pow t)
  have hn : n ^ t = n ^ (t - 1) * n := by
    rw [← pow_succ]; congr 1; omega
  have hpos : 0 < n ^ (t - 1) := by
    have : 0 < n := lt_of_le_of_lt (Nat.zero_le _) h2
    positivity
  have key : (4 * t) ^ t * n ^ (t - 1) < (4 * t) ^ t * N.choose t := by
    calc (4 * t) ^ t * n ^ (t - 1) < n * n ^ (t - 1) := Nat.mul_lt_mul_of_pos_right h2 hpos
      _ = n ^ t := by rw [hn, mul_comm]
      _ ≤ (4 * (N + 1 - t)) ^ t := Nat.pow_le_pow_left h1 t
      _ = 4 ^ t * (N + 1 - t) ^ t := mul_pow _ _ _
      _ ≤ 4 ^ t * (t ^ t * N.choose t) := Nat.mul_le_mul_left _ hc
      _ = (4 * t) ^ t * N.choose t := by rw [mul_pow]; ring
  exact Nat.lt_of_mul_lt_mul_left key

/-- **Asymptotic corollary.** For each fixed `a`, for all large `k`, a map factoring through
a commutative monoid with at most `(2^k)^a` elements has a common hole with any second map. -/
theorem monoid_factor_common_hole_eventually (a : ℕ) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ (U M : Type) [Fintype U] [DecidableEq U] [CommMonoid M] [Fintype M],
      Fintype.card U = 2 ^ k → Fintype.card M ≤ (2 ^ k) ^ a →
      ∀ (v : U → M) (ψ : M → U) (g : Finset U → U),
        ∃ Y : Finset U, #Y = k ∧ ∃ u : U,
          u ∉ Y.powerset.image (fun A => ψ (∏ x ∈ A, v x)) ∧ u ∉ Y.powerset.image g := by
  set t := a + 1 with ht
  set b := 2 ^ (2 * t) with hb
  set d := 6 * b with hd
  refine ⟨(4 * t) ^ t + 8 * (t * d) + 3, fun k hk U M _ _ _ _ hU hM v ψ g => ?_⟩
  have hb2 : 2 ≤ b := by
    rw [hb]; calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd1 : 1 ≤ d := by omega
  have hnk : k < 2 ^ k := Nat.lt_two_pow_self
  have htd : t ≤ t * d := Nat.le_mul_of_pos_right _ hd1
  have hmul : 2 * t * (d - 1) = 2 * (t * d) - 2 * t := by
    rw [Nat.mul_sub, mul_one, mul_assoc]
  have h7 : Fintype.card M < (2 ^ k - 2 * t * (d - 1)).choose t := by
    refine lt_of_le_of_lt hM ?_
    have := choose_big (2 ^ k) (2 ^ k - 2 * t * (d - 1)) t (by omega) (by omega) (by omega)
    simpa [ht] using this
  exact one_structured_map_hole_gen k t d (by omega) hU v ψ h7 (by rw [mul_assoc]; omega)
    (sixtyfour_le b hb2) g

end E624R6

namespace E624R6
open Finset

/-- Bonferroni at depth 5: `[m = 0] ≥ Σ_{j ≤ 5} (-1)^j C(m, j)`. -/
lemma bonf5 (m : ℕ) :
    (1 : ℤ) - m + m.choose 2 - m.choose 3 + m.choose 4 - m.choose 5 ≤ if m = 0 then 1 else 0 := by
  rcases m with _ | m
  · simp
  · simp only [Nat.succ_ne_zero, if_false]
    have e : ((1 : ℤ) - ((m + 1 : ℕ) : ℤ) + ((m + 1).choose 2 : ℕ) - ((m + 1).choose 3 : ℕ) +
        ((m + 1).choose 4 : ℕ) - ((m + 1).choose 5 : ℕ)) = -((m.choose 5 : ℕ) : ℤ) := by
      simp only [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast; ring
    rw [e]; simp

section FiveMoment
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma face_bound (k : ℕ) (hU : Fintype.card U = 2 ^ k) (g : Fin 2 → Finset U → U)
    (Y : Finset U) (hY : #Y = k) :
    -(2 ^ k : ℤ) + (∑ u, (#((univ ×ˢ Y.powerset).filter
          (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 2 : ℕ)
      - (∑ u, (#((univ ×ˢ Y.powerset).filter
          (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 3 : ℕ)
      + (∑ u, (#((univ ×ˢ Y.powerset).filter
          (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 4 : ℕ)
      - (∑ u, (#((univ ×ˢ Y.powerset).filter
          (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 5 : ℕ) ≤
    ((2 ^ k - #(Y.powerset.image (g 0) ∪ Y.powerset.image (g 1)) : ℕ) : ℤ) := by
  set m : U → ℕ := fun u => #((univ ×ˢ Y.powerset).filter
    (fun p : Fin 2 × Finset U => g p.1 p.2 = u)) with hm
  set S := Y.powerset.image (g 0) ∪ Y.powerset.image (g 1) with hS
  -- total evaluations
  have htot : ∑ u, m u = 2 * 2 ^ k := by
    have := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin 2)) ×ˢ Y.powerset)
      (t := (univ : Finset U)) (f := fun p => g p.1 p.2) (fun _ _ => mem_coe.2 (mem_univ _))
    rw [card_product, card_univ, Fintype.card_fin, card_powerset, hY] at this
    rw [this]
  -- zero set
  have hzero : (univ : Finset U).filter (fun u => m u = 0) = univ \ S := by
    ext u
    rw [mem_filter, mem_sdiff]
    simp only [mem_univ, true_and]
    constructor
    · intro h hu
      have hpos : 0 < m u := by
        rw [hS, mem_union] at hu
        rcases hu with hu | hu
        · obtain ⟨A, hA, he⟩ := mem_image.1 hu
          exact card_pos.2 ⟨((0 : Fin 2), A), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, hA⟩, he⟩⟩
        · obtain ⟨A, hA, he⟩ := mem_image.1 hu
          exact card_pos.2 ⟨((1 : Fin 2), A), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, hA⟩, he⟩⟩
      omega
    · intro hu
      apply card_eq_zero.2
      apply filter_eq_empty_iff.2
      rintro ⟨i, A⟩ hp heq
      have hA := (mem_product.1 hp).2
      apply hu
      rw [hS, mem_union]
      fin_cases i
      · exact Or.inl (mem_image.2 ⟨A, hA, heq⟩)
      · exact Or.inr (mem_image.2 ⟨A, hA, heq⟩)
  have hD : ((2 ^ k - #S : ℕ) : ℤ) = ∑ u, (if m u = 0 then (1 : ℤ) else 0) := by
    rw [sum_boole, hzero, card_sdiff_of_subset (subset_univ _), card_univ, hU]
  rw [hD]
  calc _ = ∑ u, ((1 : ℤ) - m u + (m u).choose 2 - (m u).choose 3 + (m u).choose 4
              - (m u).choose 5) := by
          simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, hU]
          push_cast
          have h2 : (∑ u, (m u : ℤ)) = 2 * 2 ^ k := by exact_mod_cast htot
          rw [h2]; simp; ring
    _ ≤ _ := sum_le_sum (fun u _ => bonf5 (m u))

/-- **Five-moment certificate (16) ⇒ (17).** -/
theorem five_moment_gen (k : ℕ) (hU : Fintype.card U = 2 ^ k) (g : Fin 2 → Finset U → U)
    (h2 : 239 * (2 ^ k * #(powersetCard k (univ : Finset U))) ≤
      120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 2)
    (h3 : 120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 3 ≤
      161 * (2 ^ k * #(powersetCard k (univ : Finset U))))
    (h4 : 79 * (2 ^ k * #(powersetCard k (univ : Finset U))) ≤
      120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 4)
    (h5 : 120 * ∑ Y ∈ powersetCard k (univ : Finset U), ∑ u, (#((univ ×ˢ Y.powerset).filter
        (fun p : Fin 2 × Finset U => g p.1 p.2 = u))).choose 5 ≤
      33 * (2 ^ k * #(powersetCard k (univ : Finset U)))) :
    2 ^ k * #(powersetCard k (univ : Finset U)) ≤
      30 * ∑ Y ∈ powersetCard k (univ : Finset U),
        (2 ^ k - #(Y.powerset.image (g 0) ∪ Y.powerset.image (g 1))) := by
  have hsum := sum_le_sum (s := powersetCard k (univ : Finset U)) (fun Y hY => face_bound k hU g Y (mem_powersetCard.1 hY).2)
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, sum_const, nsmul_eq_mul] at hsum
  push_cast at hsum h2 h3 h4 h5 ⊢
  linarith

end FiveMoment
end E624R6


namespace Erdos624

theorem monoid_compression {U : Type*} [Fintype U] [DecidableEq U] {M : Type*} [CommMonoid M]
    (t d : ℕ) (v : U → M) (ψ : M → U) (Bk P Q : Fin d → Finset U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) (hcard : ∀ i, #(Bk i) ≤ 2 * t)
    (hP : ∀ i, P i ⊆ Bk i) (hQ : ∀ i, Q i ⊆ Bk i) (hne : ∀ i, P i ≠ Q i)
    (heq : ∀ i, ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x)
    (Y : Finset U) (hY : (univ : Finset (Fin d)).biUnion Bk ⊆ Y) :
    (2 ^ (2 * t)) ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤
      (2 ^ (2 * t) - 1) ^ d * 2 ^ #Y :=
  by classical exact E624R6.monoid_compression_gen t d v ψ Bk P Q hdisj hcard hP hQ hne heq Y hY

end Erdos624

open Erdos624 in
theorem solution {U : Type*} [Fintype U] [DecidableEq U] {M : Type*} [CommMonoid M]
    (t d : ℕ) (v : U → M) (ψ : M → U) (Bk P Q : Fin d → Finset U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Bk i) (Bk j)) (hcard : ∀ i, #(Bk i) ≤ 2 * t)
    (hP : ∀ i, P i ⊆ Bk i) (hQ : ∀ i, Q i ⊆ Bk i) (hne : ∀ i, P i ≠ Q i)
    (heq : ∀ i, ∏ x ∈ P i, v x = ∏ x ∈ Q i, v x)
    (Y : Finset U) (hY : (univ : Finset (Fin d)).biUnion Bk ⊆ Y) :
    (2 ^ (2 * t)) ^ d * #(Y.powerset.image (fun A => ψ (∏ x ∈ A, v x))) ≤
      (2 ^ (2 * t) - 1) ^ d * 2 ^ #Y :=
  Erdos624.monoid_compression t d v ψ Bk P Q hdisj hcard hP hQ hne heq Y hY

#print axioms solution
