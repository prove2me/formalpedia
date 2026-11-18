-- Prove2me | solution 1 for EditGV897.Main.signed_code_indexing
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:47:39.831328+00:00
-- url     : https://prove2.me/submissions/40aa39c1-4d5a-446a-b3e2-9b7ccbf1b065

import Definitions.Def_EditGV897_Main_Codec


namespace EditGV897.Main

 theorem bit_zero_or_one (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl


@[simp] theorem wordList_length {n : ℕ} (x : Word n) : (wordList x).length = n := by
  simp [wordList, DeletionHash.MixedEdit.letters]

@[simp] theorem listWord_wordList {n : ℕ} (x : Word n) : listWord n (wordList x) = x := by
  funext i
  simp [listWord, wordList, DeletionHash.MixedEdit.letters]

theorem wordList_listWord {n : ℕ} (p : List Bit) (hp : p.length = n) :
    wordList (listWord n p) = p := by
  apply List.ext_getElem
  · simp [hp]
  · intro i hi hj
    simp only [wordList, DeletionHash.MixedEdit.letters, List.getElem_ofFn, listWord]
    simp [List.getElem?_eq_getElem, hj]

theorem dot_add {n : ℕ} (h x y : Word n) : dot h (x + y) = dot h x + dot h y := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem separated_of_witnesses_zero {n t : ℕ} (F : Family n) (G : Rows n)
    (hF : EditFamily t F) (x : Word n) (hx : witnessesAt F G x = 0) :
    Separated t G x := by
  classical
  intro y hxy hc hs
  obtain ⟨f, hf, hfx⟩ := hF.2.1 x y hxy hc
  have hd : differenceAt f x ≠ 0 := by
    intro hd
    apply hxy
    funext i
    have hi := congrFun hd i
    simpa only [differenceAt, Pi.add_apply, hfx, Pi.zero_apply,
      CharTwo.add_eq_zero] using hi
  have hz : syndrome G (differenceAt f x) = G.map (fun _ => 0) := by
    unfold syndrome
    apply List.map_congr_left
    intro h hh
    have hsy : dot h x = dot h y := by
      have hi := List.map_inj_left.mp hs h hh
      exact hi
    simp only [differenceAt, hfx, dot_add, hsy, CharTwo.add_self_eq_zero]
  have hmem : f ∈ F.filter (fun g => decide
      (differenceAt g x ≠ 0 ∧ syndrome G (differenceAt g x) = G.map (fun _ => 0))) := by
    simp [hf, hd, hz]
  have hnil : F.filter (fun g => decide
      (differenceAt g x ≠ 0 ∧ syndrome G (differenceAt g x) = G.map (fun _ => 0))) = [] :=
    List.length_eq_zero_iff.mp hx
  rw [hnil] at hmem
  exact List.not_mem_nil hmem

theorem prefixCoset_leaf {n : ℕ} (G : Rows n) (β : List Bit) (p : List Bit)
    (hp : p.length = n) :
    prefixCoset G β p = if syndrome G (listWord n p) = β then {listWord n p} else ∅ := by
  classical
  ext x
  simp only [prefixCoset, coset, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hp, List.take_of_length_le (by simp)]
  by_cases hs : syndrome G (listWord n p) = β
  · simp only [hs, ite_true, Finset.mem_singleton]
    constructor
    · intro ⟨h, hx⟩
      simpa only [listWord_wordList] using congrArg (listWord n) hx
    · intro hx
      subst x
      exact ⟨hs, wordList_listWord p hp⟩
  · simp only [hs, ite_false, Finset.notMem_empty, iff_false, not_and]
    intro hx hp'
    apply hs
    have he : x = listWord n p := by
      simpa only [listWord_wordList] using congrArg (listWord n) hp'
    simpa [← he] using hx

theorem signedBound_leaf_le {n : ℕ} (F : Family n) (G : Rows n) (β p : List Bit)
    (hp : p.length = n) : signedBound F G (prefixCoset G β p) ≤ 1 := by
  classical
  rw [prefixCoset_leaf G β p hp]
  split_ifs <;> simp [signedBound, witnessSum]

theorem signedBound_leaf_positive {n t : ℕ} (F : Family n) (G : Rows n)
    (β p : List Bit) (hp : p.length = n) (hF : EditFamily t F)
    (hpos : 0 < signedBound F G (prefixCoset G β p)) :
    syndrome G (listWord n p) = β ∧ Separated t G (listWord n p) := by
  classical
  rw [prefixCoset_leaf G β p hp] at hpos
  split_ifs at hpos with hs
  · refine ⟨hs, separated_of_witnesses_zero F G hF _ ?_⟩
    simp only [signedBound, Finset.card_singleton, Nat.cast_one, witnessSum,
      Finset.sum_singleton] at hpos
    omega
  · simp [signedBound, witnessSum] at hpos

private theorem take_child_iff (x p : List Bit) (a : Bit) (hp : p.length < x.length) :
    x.take (p ++ [a]).length = p ++ [a] ↔
      x.take p.length = p ∧ x[p.length] = a := by
  simp only [List.length_append, List.length_singleton]
  rw [List.take_succ_eq_append_getElem hp]
  constructor
  · intro he
    have hlen : (x.take p.length).length = p.length := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hp)]
    obtain ⟨h1, h2⟩ := List.append_inj he hlen
    exact ⟨h1, List.singleton_inj.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem prefixCoset_children {n : ℕ} (G : Rows n) (β p : List Bit)
    (hp : p.length < n) :
    prefixCoset G β p = prefixCoset G β (p ++ [0]) ∪ prefixCoset G β (p ++ [1]) ∧
    Disjoint (prefixCoset G β (p ++ [0])) (prefixCoset G β (p ++ [1])) := by
  classical
  have hm (x : Word n) (a : Bit) :
      x ∈ prefixCoset G β (p ++ [a]) ↔
      x ∈ prefixCoset G β p ∧ (wordList x)[p.length]'(by simpa using hp) = a := by
    simp only [prefixCoset, coset, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [take_child_iff _ p a (by simpa using hp)]
    tauto
  constructor
  · ext x
    simp only [Finset.mem_union, hm]
    have hb : (wordList x)[p.length]'(by simpa using hp) = 0 ∨
        (wordList x)[p.length]'(by simpa using hp) = 1 := by
      exact bit_zero_or_one _
    tauto
  · apply Finset.disjoint_left.mpr
    intro x h0 h1
    have he : (0 : Bit) = 1 := (hm x 0 |>.mp h0).2.symm.trans (hm x 1 |>.mp h1).2
    exact zero_ne_one he

theorem signedBound_prefix_additive {n : ℕ} (F : Family n) (G : Rows n)
    (β p : List Bit) (hp : p.length < n) :
    signedBound F G (prefixCoset G β p) =
      signedBound F G (prefixCoset G β (p ++ [0])) +
      signedBound F G (prefixCoset G β (p ++ [1])) := by
  classical
  obtain ⟨hu, hd⟩ := prefixCoset_children G β p hp
  rw [hu]
  unfold signedBound witnessSum
  rw [Finset.card_union_of_disjoint hd, Finset.sum_union hd]
  push_cast
  ring

end EditGV897.Main

namespace EditGV897.Main

theorem dot_unitWord {n k : ℕ} (x : Word n) (hk : k < n) :
    dot (unitWord n k) x = x ⟨k, hk⟩ := by
  classical
  simp only [dot, unitWord]
  have he (i : Fin n) : (if i.val = k then (1 : Bit) else 0) * x i =
      if i = ⟨k, hk⟩ then x ⟨k, hk⟩ else 0 := by
    by_cases hi : i.val = k
    · have hie : i = ⟨k, hk⟩ := Fin.ext hi
      simp [hie]
    · have hie : i ≠ ⟨k, hk⟩ := by intro h; exact hi (congrArg Fin.val h)
      simp [hi, hie]
  simp_rw [he]
  simp

theorem cosetEquations_spec {n : ℕ} (G : Rows n) (β : List Bit)
    (hβ : β.length = G.length) (x : Word n) :
    (∀ e ∈ cosetEquations G β, equationHolds e x) ↔ syndrome G x = β := by
  unfold cosetEquations syndrome
  induction G generalizing β with
  | nil =>
    have : β = [] := List.length_eq_zero_iff.mp hβ
    subst β
    simp
  | cons g G ih =>
    cases β with
    | nil => simp at hβ
    | cons a β =>
      have hl : β.length = G.length := by simpa using hβ
      simpa only [List.zip_cons_cons, List.forall_mem_cons, equationHolds, List.map_cons,
        List.cons.injEq] using and_congr Iff.rfl (ih β hl)

theorem prefixEquations_spec {n : ℕ} (p : List Bit) (hp : p.length ≤ n) (x : Word n) :
    (∀ e ∈ prefixEquations n p, equationHolds e x) ↔ (wordList x).take p.length = p := by
  simp only [prefixEquations, List.forall_mem_map, List.mem_range]
  constructor
  · intro h
    apply List.ext_getElem
    · simp [Nat.min_eq_left hp]
    · intro k hk hkp
      have hkn : k < n := lt_of_lt_of_le hkp hp
      have he := h k hkp
      simp only [equationHolds, dot_unitWord x hkn] at he
      simpa [wordList, DeletionHash.MixedEdit.letters, hkp] using he
  · intro he k hk
    have hkn : k < n := lt_of_lt_of_le hk hp
    simp only [equationHolds, dot_unitWord x hkn]
    have he' := congrArg (fun q : List Bit => q[k]?) he
    simpa [wordList, DeletionHash.MixedEdit.letters, hk, hkn] using he'

theorem affineSet_prefix {n : ℕ} (G : Rows n) (β p : List Bit)
    (hβ : β.length = G.length) (hp : p.length ≤ n) :
    affineSet (cosetEquations G β ++ prefixEquations n p) = prefixCoset G β p := by
  classical
  ext x
  simp only [affineSet, prefixCoset, coset, Finset.mem_filter, Finset.mem_univ, true_and,
    List.forall_mem_append, cosetEquations_spec G β hβ x, prefixEquations_spec p hp x]

theorem prefixBound_spec_of_counts {n : ℕ} (F : Family n) (G : Rows n) (β : List Bit)
    (hβ : β.length = G.length)
    (ha : ∀ E : List (Equation n), affineCount E = (affineSet E).card)
    (hw : ∀ E : List (Equation n), witnessCount F G E = witnessSum F G (affineSet E))
    (p : List Bit) (hp : p.length ≤ n) :
    prefixBound F G β p = signedBound F G (prefixCoset G β p) := by
  unfold prefixBound boundCount signedBound
  rw [ha, hw, affineSet_prefix G β p hβ hp]

end EditGV897.Main

namespace EditGV897.Main

/-- The signed-index invariant and exact reconstruction of the original index. -/
theorem encodeSteps_invariant {n : ℕ} (F : Family n) (P : Parameters n)
    (hadd : ∀ p : List Bit, p.length < n →
      prefixBound F P.rows P.beta p =
        prefixBound F P.rows P.beta (p ++ [0]) +
        prefixBound F P.rows P.beta (p ++ [1]))
    (hleaf : ∀ p : List Bit, p.length = n → prefixBound F P.rows P.beta p ≤ 1)
    (k : ℕ) (p : List Bit) (m : ℤ) (hlen : p.length + k = n)
    (hm : 0 ≤ m ∧ m < prefixBound F P.rows P.beta p) :
    let q := encodeSteps F P k p m
    q.1.length = n ∧ q.2 = 0 ∧ prefixBound F P.rows P.beta q.1 = 1 := by
  induction k generalizing p m with
  | zero =>
    simp only [encodeSteps]
    have hp : p.length = n := by omega
    have h := hleaf p hp
    exact ⟨hp, by omega, by omega⟩
  | succ k ih =>
    have hp : p.length < n := by omega
    have ha := hadd p hp
    simp only [encodeSteps]
    split_ifs with h
    · apply ih
      · simp only [List.length_append, List.length_singleton]; omega
      · exact ⟨hm.1, h⟩
    · apply ih
      · simp only [List.length_append, List.length_singleton]; omega
      · constructor <;> omega

private theorem inverse_fold_prefix {n : ℕ} (F : Family n) (P : Parameters n)
    (p : List Bit) :
    (p.foldl (fun s a =>
      let L := prefixBound F P.rows P.beta (s.1 ++ [0])
      (s.1 ++ [a], s.2 + if a = 0 then 0 else max 0 L))
      (([] : List Bit), (0 : ℤ))).1 = p := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p a ih =>
    simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]

theorem inverseIndex_append {n : ℕ} (F : Family n) (P : Parameters n)
    (p : List Bit) (a : Bit) :
    inverseIndex F P (p ++ [a]) = inverseIndex F P p +
      if a = 0 then 0 else max 0 (prefixBound F P.rows P.beta (p ++ [0])) := by
  simp only [inverseIndex, List.foldl_append, List.foldl_cons, List.foldl_nil,
    inverse_fold_prefix]

theorem encodeSteps_index {n : ℕ} (F : Family n) (P : Parameters n)
    (k : ℕ) (p : List Bit) (m : ℤ) :
    let q := encodeSteps F P k p m
    inverseIndex F P q.1 + q.2 = inverseIndex F P p + m := by
  induction k generalizing p m with
  | zero => rfl
  | succ k ih =>
    simp only [encodeSteps]
    split_ifs with h
    · rw [ih, inverseIndex_append]
      simp
    · rw [ih, inverseIndex_append]
      have h10 : (1 : Bit) ≠ 0 := one_ne_zero
      simp only [h10, if_false]
      omega

theorem messageIndex_append (u : List Bit) (a : Bit) :
    messageIndex (u ++ [a]) = 2 * messageIndex u + if a = 0 then 0 else 1 := by
  simp only [messageIndex, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem messageIndex_range (u : List Bit) :
    0 ≤ messageIndex u ∧ messageIndex u < 2 ^ u.length := by
  induction u using List.reverseRecOn with
  | nil => simp [messageIndex]
  | append_singleton u a ih =>
    rw [messageIndex_append]
    simp only [List.length_append, List.length_singleton, pow_succ]
    split_ifs <;> omega

theorem messageIndex_injective : ∀ (u v : List Bit), u.length = v.length →
    messageIndex u = messageIndex v → u = v := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro v hlen h
    have : v = [] := by simpa using hlen.symm
    exact this.symm
  | append_singleton u a ih =>
    intro v hlen h
    cases v using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton v b =>
      have hab : a = b := by
        rw [messageIndex_append, messageIndex_append] at h
        have ha : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
        have hb : b = 0 ∨ b = 1 := by fin_cases b <;> first | exact Or.inl rfl | exact Or.inr rfl
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          norm_num at h ⊢ <;> omega
      have huv : messageIndex u = messageIndex v := by
        rw [hab, messageIndex_append, messageIndex_append] at h
        omega
      rw [ih v (by simpa using hlen) huv, hab]

private theorem indexBits_bit (K m : ℕ) (a : Bit) :
    indexBits (K + 1) (2 * m + if a = 0 then 0 else 1) = indexBits K m ++ [a] := by
  apply List.ext_getElem
  · simp [indexBits]
  · intro i hi hj
    simp only [indexBits, List.length_map, List.length_range] at hi
    by_cases hik : i < K
    · rw [List.getElem_append_left (by simpa [indexBits] using hik)]
      simp only [indexBits, List.getElem_map, List.getElem_range]
      have he : K + 1 - 1 - i = (K - 1 - i) + 1 := by omega
      rw [he]
      have ha : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases ha with rfl | rfl
      · simp only [ite_true, add_zero]
        rw [show 2 * m = Nat.bit false m by simp [Nat.bit], Nat.testBit_bit_succ]
      · simp only [one_ne_zero, ite_false]
        rw [show 2 * m + 1 = Nat.bit true m by simp [Nat.bit], Nat.testBit_bit_succ]
    · have hie : i = K := by omega
      subst i
      rw [List.getElem_append_right (by simp [indexBits])]
      simp only [indexBits, List.getElem_map, List.getElem_range, List.length_map,
        List.length_range, Nat.sub_self, List.getElem_cons_zero]
      have he : K + 1 - 1 - K = 0 := by omega
      rw [he]
      have ha : a = 0 ∨ a = 1 := by fin_cases a <;> first | exact Or.inl rfl | exact Or.inr rfl
      rcases ha with rfl | rfl
      · simp only [ite_true, add_zero]
        rw [show 2 * m = Nat.bit false m by simp [Nat.bit], Nat.testBit_bit_zero]
        rfl
      · simp only [one_ne_zero, ite_false]
        rw [show 2 * m + 1 = Nat.bit true m by simp [Nat.bit], Nat.testBit_bit_zero]
        rfl

theorem indexBits_messageIndex (u : List Bit) :
    indexBits u.length (messageIndex u).toNat = u := by
  induction u using List.reverseRecOn with
  | nil => simp [indexBits]
  | append_singleton u a ih =>
    rw [messageIndex_append]
    have hm := (messageIndex_range u).1
    have hcast : (2 * messageIndex u + if a = 0 then 0 else 1).toNat =
        2 * (messageIndex u).toNat + if a = 0 then 0 else 1 := by
      split_ifs <;> omega
    rw [hcast]
    simpa only [List.length_append, List.length_singleton, indexBits_bit, ih]

/-- Semantic part of Lemma 3, with exact prefix counting as its interface. -/
theorem signed_bound_indexing {n t : ℕ} (F : Family n) (P : Parameters n)
    (hF : EditFamily t F)
    (hspec : ∀ p : List Bit, p.length ≤ n →
      prefixBound F P.rows P.beta p = signedBound F P.rows (prefixCoset P.rows P.beta p))
    (hroot : (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta)) :
    Function.Injective (encodeWord F P) ∧
    ∀ u : Word (messageLength P),
      encodeList F P u = wordList (encodeWord F P u) ∧ (encodeList F P u).length = n ∧
      syndrome P.rows (encodeWord F P u) = P.beta ∧ Separated t P.rows (encodeWord F P u) ∧
      (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
      inverseList F P (wordList (encodeWord F P u)) = wordList u := by
  classical
  have hadd (p : List Bit) (hp : p.length < n) :
      prefixBound F P.rows P.beta p =
        prefixBound F P.rows P.beta (p ++ [0]) + prefixBound F P.rows P.beta (p ++ [1]) := by
    rw [hspec p (by omega), hspec (p ++ [0]) (by simp; omega),
      hspec (p ++ [1]) (by simp; omega)]
    exact signedBound_prefix_additive F P.rows P.beta p hp
  have hleaf (p : List Bit) (hp : p.length = n) : prefixBound F P.rows P.beta p ≤ 1 := by
    rw [hspec p (by omega)]
    exact signedBound_leaf_le F P.rows P.beta p hp
  have hall (u : Word (messageLength P)) :
      encodeList F P u = wordList (encodeWord F P u) ∧ (encodeList F P u).length = n ∧
      syndrome P.rows (encodeWord F P u) = P.beta ∧ Separated t P.rows (encodeWord F P u) ∧
      (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
      inverseList F P (wordList (encodeWord F P u)) = wordList u := by
    have hm := messageIndex_range (wordList u)
    simp only [wordList_length] at hm
    have hstart : 0 ≤ messageIndex (wordList u) ∧
        messageIndex (wordList u) < prefixBound F P.rows P.beta [] := by
      refine ⟨hm.1, ?_⟩
      rw [hspec [] (by simp)]
      have he : prefixCoset P.rows P.beta [] = coset P.rows P.beta := by
        ext x; simp [prefixCoset]
      rw [he]
      exact lt_of_lt_of_le hm.2 hroot
    obtain ⟨hlen, hfinal, hbound⟩ := encodeSteps_invariant F P hadd hleaf n []
      (messageIndex (wordList u)) (by simp) hstart
    have hlen' : (encodeList F P u).length = n := hlen
    have hw : wordList (encodeWord F P u) = encodeList F P u :=
      wordList_listWord _ hlen'
    have hpos : 0 < signedBound F P.rows
        (prefixCoset P.rows P.beta (encodeList F P u)) := by
      rw [← hspec _ (by omega)]
      change 0 < prefixBound F P.rows P.beta
        (encodeSteps F P n [] (messageIndex (wordList u))).1
      rw [hbound]
      norm_num
    have hgood := signedBound_leaf_positive F P.rows P.beta (encodeList F P u) hlen' hF hpos
    have hinv : inverseList F P (wordList (encodeWord F P u)) = wordList u := by
      rw [hw]
      unfold inverseList
      have hi := encodeSteps_index F P n [] (messageIndex (wordList u))
      change inverseIndex F P (encodeList F P u) + _ = _ at hi
      have hi0 : inverseIndex F P [] = 0 := rfl
      simp only [hfinal, hi0, add_zero, zero_add] at hi
      rw [hi]
      simpa only [wordList_length] using indexBits_messageIndex (wordList u)
    exact ⟨hw.symm, hlen', hgood.1, hgood.2, hfinal, hinv⟩
  refine ⟨?_, hall⟩
  intro u v huv
  have hu := (hall u).2.2.2.2.2
  have hv := (hall v).2.2.2.2.2
  rw [huv, hv] at hu
  exact List.ofFn_injective hu.symm

end EditGV897.Main
open EditGV897.Main

theorem solution {n t : ℕ} (F : Family n) (P : Parameters n)
    (hF : EditFamily t F) (hβ : P.beta.length = P.rows.length)
    (ha : ∀ E : List (Equation n), affineCount E = (affineSet E).card)
    (hw : ∀ E : List (Equation n), witnessCount F P.rows E = witnessSum F P.rows (affineSet E))
    (hroot : (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta)) :
    Function.Injective (encodeWord F P) ∧
    ∀ u : Word (messageLength P),
      encodeList F P u = wordList (encodeWord F P u) ∧ (encodeList F P u).length = n ∧
      syndrome P.rows (encodeWord F P u) = P.beta ∧ Separated t P.rows (encodeWord F P u) ∧
      (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
      inverseList F P (wordList (encodeWord F P u)) = wordList u := by
  exact signed_bound_indexing F P hF (prefixBound_spec_of_counts F P.rows P.beta hβ ha hw) hroot
