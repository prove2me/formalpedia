-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:27:24.03684+00:00
-- url     : https://prove2.me/submissions/db60a120-0aac-4f89-a789-50590d2fca89

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_lemma_2

open CostSharingPNE.Char

namespace CSPLemma3Aux

variable {n : ℕ}

/-- Möbius inversion on the Boolean lattice: `W(S) = ∑_{T ⊆ S} q^W_T`. -/
lemma sum_mobius (S : Finset (Fin n)) : ∀ W : Welfare n, ∑ T ∈ S.powerset, mobius W T = W S := by
  induction S using Finset.induction_on with
  | empty => intro W; simp [mobius]
  | insert a S ha ih =>
    intro W
    rw [Finset.sum_powerset_insert ha]
    have key : ∀ T ∈ S.powerset, mobius W (insert a T) =
        - mobius W T + mobius (fun R => W (insert a R)) T := by
      intro T hT
      have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
      unfold mobius
      rw [Finset.sum_powerset_insert haT, Finset.card_insert_of_notMem haT, ← Finset.sum_neg_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro R hR
        have hRT := Finset.card_le_card (Finset.mem_powerset.mp hR)
        rw [show T.card + 1 - R.card = (T.card - R.card) + 1 by omega, pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro R hR
        have haR : a ∉ R := fun h => haT (Finset.mem_powerset.mp hR h)
        rw [Finset.card_insert_of_notMem haR]
        congr 2
        omega
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_neg_distrib, ih W,
      ih (fun R => W (insert a R))]
    ring

lemma W_eq_sum_coalitionsIn (W : Welfare n) (h0 : W ∅ = 0) (T : Finset (Fin n)) :
    W T = ∑ T' ∈ coalitionsIn W T, mobius W T' := by
  rw [← sum_mobius T W]
  symm
  apply Finset.sum_subset
  · intro T' hT'
    unfold coalitionsIn at hT'
    exact Finset.mem_powerset.mpr (Finset.mem_filter.mp hT').2
  · intro T' hT' hn
    unfold coalitionsIn coalitions at hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hn
    by_cases hne : T'.Nonempty
    · by_contra hq
      exact hn ⟨hne, hq⟩ (Finset.mem_powerset.mp hT')
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      simp [mobius, h0]

lemma mem_contributing (W : Welfare n) (S : Finset (Fin n)) (i : Fin n) :
    i ∈ contributing W S ↔ ∃ T ∈ coalitions W, T ⊆ S ∧ i ∈ T := by
  unfold contributing coalitionsIn
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨T, ⟨h1, h2⟩, h3⟩; exact ⟨T, h1, h2, h3⟩
  · rintro ⟨T, h1, h2, h3⟩; exact ⟨T, ⟨h1, h2⟩, h3⟩

lemma contributing_sub (W : Welfare n) (S : Finset (Fin n)) : contributing W S ⊆ S := by
  intro x hx
  obtain ⟨T, -, hTS, hxT⟩ := (mem_contributing W S x).mp hx
  exact hTS hxT

lemma coalitionsIn_contributing (W : Welfare n) (S : Finset (Fin n)) :
    coalitionsIn W S = coalitionsIn W (contributing W S) := by
  ext T
  unfold coalitionsIn
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hT, hTS⟩
    exact ⟨hT, fun x hx => (mem_contributing W S x).mpr ⟨T, hT, hTS, hx⟩⟩
  · rintro ⟨hT, hTS⟩
    exact ⟨hT, hTS.trans (contributing_sub W S)⟩

lemma coalitionsIn_erase (W : Welfare n) (S : Finset (Fin n)) (p : Fin n) :
    coalitionsIn W (S.erase p) = coalitionsIn W ((contributing W S).erase p) := by
  ext T
  unfold coalitionsIn
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hT, hTS⟩
    refine ⟨hT, fun x hx => ?_⟩
    rw [Finset.mem_erase]
    refine ⟨(Finset.mem_erase.mp (hTS hx)).1, ?_⟩
    exact (mem_contributing W S x).mpr
      ⟨T, hT, hTS.trans (Finset.erase_subset _ _), hx⟩
  · rintro ⟨hT, hTS⟩
    exact ⟨hT, hTS.trans (Finset.erase_subset_erase _ (contributing_sub W S))⟩

lemma contributing_erase (W : Welfare n) (S : Finset (Fin n)) (p : Fin n) :
    contributing W (S.erase p) = contributing W ((contributing W S).erase p) := by
  show (coalitionsIn W (S.erase p)).biUnion id =
    (coalitionsIn W ((contributing W S).erase p)).biUnion id
  rw [coalitionsIn_erase W S p]

/-- Counterexample 2 (p. 22): a four-resource game between `i` (rows `{r11,r12}`, `{r21,r22}`)
and `j` (columns `{r11,r21}`, `{r12,r22}`). -/
lemma cx2 (W : Welfare n) (f : Welfare n → Rule n) (hpne : GuaranteesPNE {W} f)
    (S M : Finset (Fin n)) (hMS : M ⊆ S) (i j : Fin n) (hi : i ∈ M) (hj : j ∈ M) (hij : i ≠ j)
    (h22 : f W i S < f W i M) (h23 : f W j M < f W j S)
    (h25 : f W j (S.erase i) = f W j (M.erase i))
    (h26 : f W i (S.erase j) = f W i (M.erase j)) : False := by
  classical
  let A : Fin n → Finset (Finset (Fin 4)) := fun k =>
    if k = i then {{0, 1}, {2, 3}} else if k = j then {{0, 2}, {1, 3}}
    else if k ∈ M then {Finset.univ} else if k ∈ S then {{1, 2}} else {∅}
  have hA : ∀ k, (A k).Nonempty := by
    intro k; simp only [A]; split_ifs <;> simp
  obtain ⟨a, ha, hN⟩ := hpne 4 (by norm_num) (fun _ => W) (fun _ => rfl) A hA
  have hiS := hMS hi
  have hjS := hMS hj
  have hP : ∀ (b : Fin n → Finset (Fin 4)), (∀ k, k ≠ i → k ≠ j → b k = a k) →
      ∀ r, players b r = S.filter (fun k => (k = i → r ∈ b i) ∧ (k = j → r ∈ b j) ∧
        (k ∉ M → (r = 1 ∨ r = 2))) := by
    intro b hb r
    ext k
    simp only [players, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hki : k = i
    · subst hki; simp [hiS, hi, hij]
    by_cases hkj : k = j
    · subst hkj; simp [hjS, hj, hki]
    have hak := ha k
    rw [hb k hki hkj]
    simp only [A, hki, hkj, if_false] at hak
    by_cases hkM : k ∈ M
    · rw [if_pos hkM, Finset.mem_singleton] at hak
      simp [hak, hMS hkM, hki, hkj, hkM]
    by_cases hkS : k ∈ S
    · rw [if_neg hkM, if_pos hkS, Finset.mem_singleton] at hak
      simp [hak, hkS, hki, hkj, hkM]
    · rw [if_neg hkM, if_neg hkS, Finset.mem_singleton] at hak
      simp [hak, hkS]
  have hut : ∀ (b : Fin n → Finset (Fin 4)) (k : Fin n) (x y : Fin 4), x ≠ y →
      b k = {x, y} → utility (fun _ => W) f b k = f W k (players b x) + f W k (players b y) := by
    intro b k x y hxy hb; unfold utility; rw [hb, Finset.sum_pair hxy]
  have hai := ha i
  have haj := ha j
  simp only [A, if_true, if_neg (Ne.symm hij), Finset.mem_insert, Finset.mem_singleton] at hai haj
  have hrefl : ∀ k, k ≠ i → k ≠ j → a k = a k := fun _ _ _ => rfl
  -- profile after `i` deviates
  have dev_i : ∀ x y : Fin 4, ({x, y} : Finset (Fin 4)) ∈ A i →
      (∀ k, k ≠ i → k ≠ j → Function.update a i {x, y} k = a k) ∧
      Function.update a i {x, y} i = {x, y} ∧ Function.update a i {x, y} j = a j := by
    intro x y _
    refine ⟨fun k hk _ => Function.update_of_ne hk _ _, by simp, Function.update_of_ne
      (Ne.symm hij) _ _⟩
  have dev_j : ∀ x y : Fin 4, ({x, y} : Finset (Fin 4)) ∈ A j →
      (∀ k, k ≠ i → k ≠ j → Function.update a j {x, y} k = a k) ∧
      Function.update a j {x, y} j = {x, y} ∧ Function.update a j {x, y} i = a i := by
    intro x y _
    refine ⟨fun k _ hk => Function.update_of_ne hk _ _, by simp, Function.update_of_ne
      hij _ _⟩
  have hAi1 : ({0, 1} : Finset (Fin 4)) ∈ A i := by simp [A]
  have hAi2 : ({2, 3} : Finset (Fin 4)) ∈ A i := by simp [A]
  have hAj1 : ({0, 2} : Finset (Fin 4)) ∈ A j := by simp [A, Ne.symm hij]
  have hAj2 : ({1, 3} : Finset (Fin 4)) ∈ A j := by simp [A, Ne.symm hij]
  rcases hai with hai | hai <;> rcases haj with haj | haj
  · -- TL: j deviates to R
    have hdev := hN j {1, 3} hAj2
    obtain ⟨hbo, hbj, hbi⟩ := dev_j 1 3 hAj2
    rw [hut _ j 1 3 (by decide) hbj, hut a j 0 2 (by decide) haj] at hdev
    rw [hP _ hbo 1, hP _ hbo 3, hP a hrefl 0, hP a hrefl 2] at hdev
    rw [hbi, hbj, hai, haj] at hdev
    have e1 : S.filter (fun k => (k = i → (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((1 : Fin 4) = 1 ∨
          (1 : Fin 4) = 2))) = S := by
      ext k; simp
    have e2 : S.filter (fun k => (k = i → (3 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((3 : Fin 4) = 1 ∨
          (3 : Fin 4) = 2))) = M.erase i := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      have := @hMS k; simp; tauto
    have e3 : S.filter (fun k => (k = i → (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((0 : Fin 4) = 1 ∨
          (0 : Fin 4) = 2))) = M := by
      ext k; simp only [Finset.mem_filter]
      have := @hMS k; simp; tauto
    have e4 : S.filter (fun k => (k = i → (2 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((2 : Fin 4) = 1 ∨
          (2 : Fin 4) = 2))) = S.erase i := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      simp; tauto
    rw [e1, e2, e3, e4] at hdev
    linarith
  · -- TR: i deviates to B
    have hdev := hN i {2, 3} hAi2
    obtain ⟨hbo, hbi, hbj⟩ := dev_i 2 3 hAi2
    rw [hut _ i 2 3 (by decide) hbi, hut a i 0 1 (by decide) hai] at hdev
    rw [hP _ hbo 2, hP _ hbo 3, hP a hrefl 0, hP a hrefl 1] at hdev
    rw [hbi, hbj, hai, haj] at hdev
    have e1 : S.filter (fun k => (k = i → (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (2 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((2 : Fin 4) = 1 ∨
          (2 : Fin 4) = 2))) = S.erase j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      simp; tauto
    have e2 : S.filter (fun k => (k = i → (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((3 : Fin 4) = 1 ∨
          (3 : Fin 4) = 2))) = M := by
      ext k; simp only [Finset.mem_filter]
      have := @hMS k; simp; tauto
    have e3 : S.filter (fun k => (k = i → (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (0 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((0 : Fin 4) = 1 ∨
          (0 : Fin 4) = 2))) = M.erase j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      have := @hMS k; simp; tauto
    have e4 : S.filter (fun k => (k = i → (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((1 : Fin 4) = 1 ∨
          (1 : Fin 4) = 2))) = S := by
      ext k; simp
    rw [e1, e2, e3, e4] at hdev
    linarith
  · -- BL: i deviates to T
    have hdev := hN i {0, 1} hAi1
    obtain ⟨hbo, hbi, hbj⟩ := dev_i 0 1 hAi1
    rw [hut _ i 0 1 (by decide) hbi, hut a i 2 3 (by decide) hai] at hdev
    rw [hP _ hbo 0, hP _ hbo 1, hP a hrefl 2, hP a hrefl 3] at hdev
    rw [hbi, hbj, hai, haj] at hdev
    have e1 : S.filter (fun k => (k = i → (0 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((0 : Fin 4) = 1 ∨
          (0 : Fin 4) = 2))) = M := by
      ext k; simp only [Finset.mem_filter]
      have := @hMS k; simp; tauto
    have e2 : S.filter (fun k => (k = i → (1 : Fin 4) ∈ ({0, 1} : Finset (Fin 4))) ∧
        (k = j → (1 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((1 : Fin 4) = 1 ∨
          (1 : Fin 4) = 2))) = S.erase j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      simp; tauto
    have e3 : S.filter (fun k => (k = i → (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((2 : Fin 4) = 1 ∨
          (2 : Fin 4) = 2))) = S := by
      ext k; simp
    have e4 : S.filter (fun k => (k = i → (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (3 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((3 : Fin 4) = 1 ∨
          (3 : Fin 4) = 2))) = M.erase j := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      have := @hMS k; simp; tauto
    rw [e1, e2, e3, e4] at hdev
    linarith
  · -- BR: j deviates to L
    have hdev := hN j {0, 2} hAj1
    obtain ⟨hbo, hbj, hbi⟩ := dev_j 0 2 hAj1
    rw [hut _ j 0 2 (by decide) hbj, hut a j 1 3 (by decide) haj] at hdev
    rw [hP _ hbo 0, hP _ hbo 2, hP a hrefl 1, hP a hrefl 3] at hdev
    rw [hbi, hbj, hai, haj] at hdev
    have e1 : S.filter (fun k => (k = i → (0 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (0 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((0 : Fin 4) = 1 ∨
          (0 : Fin 4) = 2))) = M.erase i := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      have := @hMS k; simp; tauto
    have e2 : S.filter (fun k => (k = i → (2 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (2 : Fin 4) ∈ ({0, 2} : Finset (Fin 4))) ∧ (k ∉ M → ((2 : Fin 4) = 1 ∨
          (2 : Fin 4) = 2))) = S := by
      ext k; simp
    have e3 : S.filter (fun k => (k = i → (1 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (1 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((1 : Fin 4) = 1 ∨
          (1 : Fin 4) = 2))) = S.erase i := by
      ext k; simp only [Finset.mem_filter, Finset.mem_erase]
      simp; tauto
    have e4 : S.filter (fun k => (k = i → (3 : Fin 4) ∈ ({2, 3} : Finset (Fin 4))) ∧
        (k = j → (3 : Fin 4) ∈ ({1, 3} : Finset (Fin 4))) ∧ (k ∉ M → ((3 : Fin 4) = 1 ∨
          (3 : Fin 4) = 2))) = M := by
      ext k; simp only [Finset.mem_filter]
      have := @hMS k; simp; tauto
    rw [e1, e2, e3, e4] at hdev
    linarith

end CSPLemma3Aux

open CSPLemma3Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hpne : GuaranteesPNE {W} f) :
    ∀ S : Finset (Fin n), ∀ i ∈ contributing W S,
      f W i S = f W i (contributing W S) := by
  have hW0 : W ∅ = 0 := by have := hbb ∅; simpa using this.symm
  have hz : ∀ (S : Finset (Fin n)), ∀ k ∈ S, k ∉ contributing W S → f W k S = 0 :=
    fun S k hk hkc => lemma_2 n hn W f hbb hpne S k (Finset.mem_sdiff.mpr ⟨hk, hkc⟩)
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    set M := contributing W S with hM
    have hMS : M ⊆ S := contributing_sub W S
    intro k hk
    by_contra hne
    -- (21): equal totals on `N(S)`
    have hWM : W S = W M := by
      rw [W_eq_sum_coalitionsIn W hW0 S, W_eq_sum_coalitionsIn W hW0 M,
        coalitionsIn_contributing W S]
    have hsum : ∑ x ∈ M, f W x S = ∑ x ∈ M, f W x M := by
      rw [hbb M, ← hWM, ← hbb S]
      apply Finset.sum_subset hMS
      intro x hxS hxM
      exact hz S x hxS hxM
    obtain ⟨i, hi, h22⟩ : ∃ i ∈ M, f W i S < f W i M := by
      by_contra hc
      push Not at hc
      have := (Finset.sum_eq_sum_iff_of_le hc).mp hsum.symm k hk
      exact hne this.symm
    obtain ⟨j, hj, h23⟩ : ∃ j ∈ M, f W j M < f W j S := by
      by_contra hc
      push Not at hc
      have := (Finset.sum_eq_sum_iff_of_le hc).mp hsum k hk
      exact hne this
    have hij : i ≠ j := by
      rintro rfl
      linarith
    -- (25), (26)
    have hswap : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → f W q (S.erase p) = f W q (M.erase p) := by
      intro p hp q hq hpq
      have hpS := hMS hp
      have hs1 : S.erase p ⊂ S := Finset.erase_ssubset hpS
      have hs2 : M.erase p ⊂ S :=
        Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset_erase p hMS) hs1
      have hNe := contributing_erase W S p
      have hq1 : q ∈ S.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hMS hq⟩
      have hq2 : q ∈ M.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpq, hq⟩
      by_cases hqc : q ∈ contributing W (S.erase p)
      · rw [ih _ hs1 q hqc, ih _ hs2 q (hNe ▸ hqc), hNe]
      · rw [hz _ q hq1 hqc, hz _ q hq2 (hNe ▸ hqc)]
    exact cx2 W f hpne S M hMS i j hi hj hij h22 h23 (hswap i hi j hj hij)
      (hswap j hj i hi (Ne.symm hij))
