-- Prove2me | solution 1 for ConstrNestedLogit.Card.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T14:16:59.979744+00:00
-- url     : https://prove2.me/submissions/3b46d96e-685f-49e5-8c25-1931c3bbb7bc

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model
import Definitions.Def_ConstrNestedLogit_Card_Knapsack

set_option autoImplicit false

namespace C21d8

open NestedLogitVariants.LP ConstrNestedLogit.Card

/-- Strict total order "k beats j": larger value first, ties broken by index. -/
def B {n : ℕ} (f : Fin n → ℝ) (k j : Fin n) : Prop := f j < f k ∨ (f k = f j ∧ k < j)

lemma B_irrefl {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : ¬ B f j j := by
  rintro (h | ⟨_, h⟩) <;> exact lt_irrefl _ h

lemma B_trans {n : ℕ} (f : Fin n → ℝ) {l k j : Fin n} (h1 : B f l k) (h2 : B f k j) :
    B f l j := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, lt_trans h1' h2'⟩

lemma B_total {n : ℕ} (f : Fin n → ℝ) {k j : Fin n} (h : k ≠ j) : B f k j ∨ B f j k := by
  rcases lt_trichotomy (f j) (f k) with h1 | h1 | h1
  · left; left; exact h1
  · rcases lt_or_gt_of_ne h with h2 | h2
    · left; right; exact ⟨h1.symm, h2⟩
    · right; right; exact ⟨h1, h2⟩
  · right; left; exact h1

lemma B_le {n : ℕ} (f : Fin n → ℝ) {k j : Fin n} (h : B f k j) : f j ≤ f k := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

open Classical in
/-- The elements beating `j`. -/
noncomputable def rk {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => B f k j)

open Classical in
/-- The greedy set: positive elements of rank below `c`. -/
noncomputable def top {n : ℕ} (f : Fin n → ℝ) (c : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => 0 < f j ∧ (rk f j).card < c)

lemma mem_rk {n : ℕ} (f : Fin n → ℝ) (k j : Fin n) : k ∈ rk f j ↔ B f k j := by
  simp [rk]

lemma mem_top {n : ℕ} (f : Fin n → ℝ) (c : ℕ) (j : Fin n) :
    j ∈ top f c ↔ 0 < f j ∧ (rk f j).card < c := by
  simp [top]

lemma rk_lt {n : ℕ} (f : Fin n → ℝ) {k j : Fin n} (h : B f k j) :
    (rk f k).card < (rk f j).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨k, (mem_rk f k j).2 h, fun hk => B_irrefl f k ((mem_rk f k k).1 hk)⟩
  · intro l hl
    rw [mem_rk] at hl ⊢
    exact B_trans f hl h

lemma top_card {n : ℕ} (f : Fin n → ℝ) (c : ℕ) : (top f c).card ≤ c := by
  have : (top f c).card ≤ (Finset.range c).card := by
    apply Finset.card_le_card_of_injOn (fun j => (rk f j).card)
    · intro j hj
      rw [Finset.mem_coe] at hj
      simp only [Finset.mem_coe, Finset.mem_range]
      exact ((mem_top f c j).1 hj).2
    · intro j _ j' _ heq
      by_contra hne
      simp only at heq
      rcases B_total f hne with h | h
      · have := rk_lt f h; omega
      · have := rk_lt f h; omega
  simpa using this

lemma top_opt {n : ℕ} (f : Fin n → ℝ) (c : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ c) :
    ∑ j ∈ S, f j ≤ ∑ j ∈ top f c, f j := by
  classical
  set T := top f c with hT
  have hTpos : ∀ j ∈ T, 0 < f j := fun j hj => ((mem_top f c j).1 hj).1
  set S2 := S.filter (fun j => 0 < f j) with hS2
  have h1 : ∑ j ∈ S, f j ≤ ∑ j ∈ S2, f j := by
    have := Finset.sum_filter_add_sum_filter_not S (fun j => 0 < f j) f
    have h0 : ∑ j ∈ S.filter (fun j => ¬ 0 < f j), f j ≤ 0 :=
      Finset.sum_nonpos (fun j hj => le_of_not_gt (Finset.mem_filter.1 hj).2)
    linarith
  refine h1.trans ?_
  set P := (Finset.univ.filter (fun j => 0 < f j)) \ T with hP
  by_cases hPe : P = ∅
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      have hj' := Finset.mem_filter.1 hj
      by_contra hjT
      have : j ∈ P := by simp [hP, hj'.2, hjT]
      rw [hPe] at this
      simp at this
    · intro j hj _
      exact (hTpos j hj).le
  · obtain ⟨j1, hj1P, hj1min⟩ := Finset.exists_min_image P (fun j => (rk f j).card)
      (Finset.nonempty_iff_ne_empty.2 hPe)
    have hj1 : 0 < f j1 ∧ j1 ∉ T := by simpa [hP] using hj1P
    have hj1c : c ≤ (rk f j1).card := by
      by_contra h
      push Not at h
      exact hj1.2 ((mem_top f c j1).2 ⟨hj1.1, h⟩)
    have hTB : ∀ l ∈ T, B f l j1 := by
      intro l hl
      have hlc := ((mem_top f c l).1 hl).2
      have hne : l ≠ j1 := fun h => hj1.2 (h ▸ hl)
      rcases B_total f hne with h | h
      · exact h
      · have := rk_lt f h; omega
    have hPB : ∀ j ∈ P, f j ≤ f j1 := by
      intro j hj
      by_cases hne : j = j1
      · rw [hne]
      rcases B_total f hne with h | h
      · have := rk_lt f h
        have := hj1min j hj
        omega
      · exact B_le f h
    have hTc : c ≤ T.card := by
      refine hj1c.trans (Finset.card_le_card ?_)
      intro k hk
      have hk' := (mem_rk f k j1).1 hk
      have hfk : 0 < f k := lt_of_lt_of_le hj1.1 (B_le f hk')
      by_contra hkT
      have hkP : k ∈ P := by simp [hP, hfk, hkT]
      have := rk_lt f hk'
      have := hj1min k hkP
      omega
    have hD : ∀ j ∈ S2 \ T, f j ≤ f j1 := by
      intro j hj
      rw [Finset.mem_sdiff] at hj
      apply hPB
      simp [hP, (Finset.mem_filter.1 hj.1).2, hj.2]
    have hE : ∀ l ∈ T \ S2, f j1 ≤ f l := fun l hl => B_le f (hTB l (Finset.mem_sdiff.1 hl).1)
    have hcard : (S2 \ T).card ≤ (T \ S2).card := by
      have a1 := Finset.card_sdiff_add_card_inter S2 T
      have a2 := Finset.card_sdiff_add_card_inter T S2
      have a3 : S2.card ≤ S.card := Finset.card_filter_le _ _
      rw [Finset.inter_comm] at a2
      omega
    have s1 := Finset.sum_le_card_nsmul (S2 \ T) f (f j1) hD
    have s2 := Finset.card_nsmul_le_sum (T \ S2) f (f j1) hE
    rw [nsmul_eq_mul] at s1 s2
    have s3 : ((S2 \ T).card : ℝ) * f j1 ≤ ((T \ S2).card : ℝ) * f j1 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hj1.1.le
    have e1 := Finset.sum_sdiff (f := f) (Finset.inter_subset_left : S2 ∩ T ⊆ S2)
    have e2 := Finset.sum_sdiff (f := f) (Finset.inter_subset_right : S2 ∩ T ⊆ T)
    have q1 : S2 \ (S2 ∩ T) = S2 \ T := by ext; simp
    have q2 : T \ (S2 ∩ T) = T \ S2 := by
      ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [q1] at e1
    rw [q2] at e2
    linarith

/-- Chain lemma: monotone Boolean signatures take at most `|κ| + 1` values. -/
lemma chain_card {κ : Type*} [Fintype κ] (Q : κ → ℝ → Bool)
    (hQ : ∀ k u u', u ≤ u' → Q k u = true → Q k u' = true) (s : Finset (κ → Bool))
    (hs : ∀ σ ∈ s, ∃ u : ℝ, (fun k => Q k u) = σ) : s.card ≤ Fintype.card κ + 1 := by
  classical
  have key : ∀ a b : ℝ, a ≤ b →
      (Finset.univ.filter (fun k => Q k a = true)).card =
        (Finset.univ.filter (fun k => Q k b = true)).card →
      (fun k => Q k a) = (fun k => Q k b) := by
    intro a b hab hc
    have hsub : Finset.univ.filter (fun k => Q k a = true) ⊆
        Finset.univ.filter (fun k => Q k b = true) := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hQ k a b hab hk
    have heq2 := Finset.eq_of_subset_of_card_le hsub hc.ge
    funext k
    have := (Finset.ext_iff.1 heq2) k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact Bool.eq_iff_iff.mpr this
  have h := Finset.card_le_card_of_injOn (s := s) (t := Finset.range (Fintype.card κ + 1))
    (fun σ => (Finset.univ.filter (fun k => σ k = true)).card) ?_ ?_
  · simpa using h
  · intro σ _
    simp only [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Finset.card_le_univ _)
  · intro σ1 h1 σ2 h2 heq
    rw [Finset.mem_coe] at h1 h2
    obtain ⟨u1, rfl⟩ := hs σ1 h1
    obtain ⟨u2, rfl⟩ := hs σ2 h2
    simp only at heq
    rcases le_total u1 u2 with h | h
    · exact key u1 u2 h heq
    · exact (key u2 u1 h heq.symm).symm

open Classical in
/-- Monotone signature of the line arrangement at `u`. -/
noncomputable def sig {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (u : ℝ) :
    Fin n ⊕ (Fin n × Fin n) → Bool
  | Sum.inl j => decide (utility I i j u ≤ 0)
  | Sum.inr (k, j) => if I.v i k ≤ I.v i j then decide (B (fun l => utility I i l u) k j)
      else !decide (B (fun l => utility I i l u) k j)

open Classical in
/-- Decoder from a signature to the greedy set. -/
noncomputable def dec {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (c : ℕ)
    (σ : Fin n ⊕ (Fin n × Fin n) → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun j => σ (Sum.inl j) = false ∧
    (Finset.univ.filter (fun k => (if I.v i k ≤ I.v i j then σ (Sum.inr (k, j))
      else !σ (Sum.inr (k, j))) = true)).card < c)

lemma dec_sig {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (c : ℕ) (u : ℝ) :
    dec I i c (sig I i u) = top (fun l => utility I i l u) c := by
  classical
  ext j
  rw [mem_top]
  simp only [dec, Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : (sig I i u (Sum.inl j) = false) ↔ 0 < utility I i j u := by
    simp [sig, not_le]
  have h2 : (Finset.univ.filter (fun k => (if I.v i k ≤ I.v i j then sig I i u (Sum.inr (k, j))
      else !sig I i u (Sum.inr (k, j))) = true)) = rk (fun l => utility I i l u) j := by
    rw [rk]
    apply Finset.filter_congr
    intro k _
    by_cases hkj : I.v i k ≤ I.v i j
    · rw [if_pos hkj]
      simp only [sig, if_pos hkj, decide_eq_true_eq]
    · rw [if_neg hkj]
      simp only [sig, if_neg hkj, Bool.not_not, decide_eq_true_eq]
  rw [h1, h2]

lemma sig_mono {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (hv : ∀ j, 0 < I.v i j)
    (x : Fin n ⊕ (Fin n × Fin n)) (u u' : ℝ) (huu : u ≤ u') (h : sig I i u x = true) :
    sig I i u' x = true := by
  rcases x with j | ⟨k, j⟩
  · have h' : utility I i j u ≤ 0 := by simpa [sig] using h
    suffices utility I i j u' ≤ 0 by simpa [sig] using this
    simp only [utility] at h' ⊢
    have := hv j
    nlinarith
  · have e : utility I i k u' - utility I i j u' =
        (utility I i k u - utility I i j u) - (I.v i k - I.v i j) * (u' - u) := by
      simp only [utility]; ring
    simp only [sig] at h ⊢
    split_ifs at h ⊢ with hkj
    · have h' : B (fun l => utility I i l u) k j := by simpa using h
      suffices B (fun l => utility I i l u') k j by simpa using this
      have hm : (I.v i k - I.v i j) * (u' - u) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
      simp only [B] at h' ⊢
      rcases h' with h' | ⟨h', hlt⟩
      · left; linarith
      · rcases lt_or_eq_of_le (show utility I i j u' ≤ utility I i k u' by linarith) with h'' | h''
        · left; exact h''
        · right; exact ⟨h''.symm, hlt⟩
    · have h' : ¬ B (fun l => utility I i l u) k j := by simpa using h
      suffices ¬ B (fun l => utility I i l u') k j by simpa using this
      have hm : 0 ≤ (I.v i k - I.v i j) * (u' - u) :=
        mul_nonneg (by push Not at hkj; linarith) (by linarith)
      intro hc
      apply h'
      simp only [B] at hc ⊢
      rcases hc with hc | ⟨hc, hlt⟩
      · left; linarith
      · rcases lt_or_eq_of_le (show utility I i j u ≤ utility I i k u by linarith) with h'' | h''
        · left; exact h''
        · right; exact ⟨h''.symm, hlt⟩

lemma obj7_eq {ι : Type*} {n : ℕ} (I : Instance ι n) (i : ι) (hvnp : I.vnp i = 0)
    (hv : ∀ j, 0 < I.v i j) (u : ℝ) (X : Finset (Fin n)) :
    V I i X * (R I i X - u) = ∑ j ∈ X, utility I i j u := by
  simp only [R, V, hvnp, zero_add, utility]
  by_cases hX : X = ∅
  · subst hX; simp
  have hpos : 0 < ∑ j ∈ X, I.v i j :=
    Finset.sum_pos (fun j _ => hv j) (Finset.nonempty_iff_ne_empty.mpr hX)
  have h1 : (∑ j ∈ X, I.v i j) * ((∑ j ∈ X, I.r i j * I.v i j) / ∑ j ∈ X, I.v i j)
      = ∑ j ∈ X, I.r i j * I.v i j := by field_simp
  rw [mul_sub, h1, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _; ring

end C21d8

open NestedLogitVariants.LP ConstrNestedLogit.Card in
theorem solution {ι : Type*} {n : ℕ} (I : Instance ι n) (c : ι → ℕ) (i : ι)
    (hvnp : I.vnp i = 0) (hv : ∀ j, 0 < I.v i j) :
    ∃ A : Finset (Finset (Fin n)), (∀ S ∈ A, S.card ≤ c i) ∧ A.card ≤ (n + 1) ^ 2 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, IsOptimal7 I c i u S := by
  classical
  let Sig := Finset.univ.filter
    (fun σ : Fin n ⊕ (Fin n × Fin n) → Bool => ∃ u : ℝ, C21d8.sig I i u = σ)
  refine ⟨Sig.image (C21d8.dec I i (c i)), ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hS
    obtain ⟨u, rfl⟩ := (Finset.mem_filter.1 hσ).2
    rw [C21d8.dec_sig]
    exact C21d8.top_card _ _
  · have h1 := Finset.card_image_le (s := Sig) (f := C21d8.dec I i (c i))
    have h2 := C21d8.chain_card (fun k u => C21d8.sig I i u k)
      (fun k u u' h hk => C21d8.sig_mono I i hv k u u' h hk) Sig
      (fun σ hσ => by
        obtain ⟨u, hu⟩ := (Finset.mem_filter.1 hσ).2
        exact ⟨u, hu⟩)
    have h3 : Fintype.card (Fin n ⊕ (Fin n × Fin n)) = n + n * n := by simp
    rw [h3] at h2
    have h4 : n + n * n + 1 ≤ (n + 1) ^ 2 := by nlinarith
    exact h1.trans (h2.trans h4)
  · intro u _
    refine ⟨C21d8.top (fun l => utility I i l u) (c i), ?_, ?_⟩
    · rw [← C21d8.dec_sig I i (c i) u]
      exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, u, rfl⟩)
    · refine ⟨C21d8.top_card _ _, fun S' hS' => ?_⟩
      rw [C21d8.obj7_eq I i hvnp hv, C21d8.obj7_eq I i hvnp hv]
      exact C21d8.top_opt _ _ S' hS'
