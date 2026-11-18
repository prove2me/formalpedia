-- Prove2me | solution 1 for EditGV897.Main.partial_row_semantics
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:48:30.170924+00:00
-- url     : https://prove2.me/submissions/796e3f43-3d61-4bb3-9d74-26e16f185814

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_affine_count_correct

import Theorems.Thm_EditGV897_Main_witness_count_correct


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
 theorem dot_add_left {n : ℕ} (x y h : Word n) : dot (x + y) h = dot x h + dot y h := by
  simp [dot, add_mul, Finset.sum_add_distrib]
end EditGV897.Main


namespace EditGV897.Main

 theorem difference_apply {n : ℕ} (f : Affine n) (x : Word n) :
    (difference f).apply x = differenceAt f x := by
  classical
  funext i
  simp only [Affine.apply, difference, differenceAt, Pi.add_apply]
  unfold dot
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp [add_assoc]

 theorem pullZero_spec {n : ℕ} (d : Affine n) (h x : Word n) :
    equationHolds (pullZero d h) x ↔ dot h (d.apply x) = 0 := by
  have he : dot (fun j => ∑ i, h i * d.matrix i j) x =
      ∑ i, h i * dot (d.matrix i) x := by
    simp only [dot, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  unfold equationHolds pullZero
  simp only
  rw [he]
  have he' : dot h (d.apply x) = (∑ i, h i * dot (d.matrix i) x) + dot h d.offset := by
    simp [dot, Affine.apply, mul_add, Finset.sum_add_distrib]
  rw [he', CharTwo.add_eq_zero]

 theorem fixedEquations_spec {n : ℕ} (f : Affine n) (x : Word n) :
    (∀ e ∈ fixedEquations f, equationHolds e x) ↔ differenceAt f x = 0 := by
  rw [← difference_apply]
  constructor
  · intro h
    funext i
    have hi := h ((difference f).matrix i, f.offset i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    change dot ((difference f).matrix i) x + f.offset i = 0
    exact CharTwo.add_eq_zero.mpr hi
  · intro h e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    have hi := congrFun h i
    change dot ((difference f).matrix i) x + f.offset i = 0 at hi
    exact CharTwo.add_eq_zero.mp hi

 theorem collisionEquations_spec {n : ℕ} (f : Affine n) (G : Rows n) (x : Word n) :
    (∀ e ∈ collisionEquations f G, equationHolds e x) ↔
      syndrome G (differenceAt f x) = G.map (fun _ => 0) := by
  simp only [collisionEquations, List.forall_mem_map, pullZero_spec, difference_apply,
    syndrome, List.map_eq_map_iff]

private theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witness_count_correct n F G E
end EditGV897.Main

namespace EditGV897.Main
 theorem syndrome_append_zero {n : ℕ} (G : Rows n) (h d : Word n) :
    syndrome (G ++ [h]) d = (G ++ [h]).map (fun _ => 0) ↔
      syndrome G d = G.map (fun _ => 0) ∧ dot h d = 0 := by
  simp only [syndrome, List.map_append, List.map_cons, List.map_nil]
  constructor
  · intro he
    obtain ⟨h1, h2⟩ := List.append_inj he (by simp)
    exact ⟨h1, List.singleton_inj.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]


end EditGV897.Main


namespace EditGV897.Main

open Classical

private def suffixZero {n : ℕ} (d : Word n) (j : ℕ) : Prop := ∀ i : Fin n, j ≤ i.val → d i = 0

private noncomputable def partialContribution {n : ℕ} (d : Word n) (p : List Bit) : ℤ := by
  classical
  exact if suffixZero d p.length then if dot (listWord n p) d = 0 then 2 else 0 else 1

private theorem listWord_append {n : ℕ} (p : List Bit) (a : Bit) :
    listWord n (p ++ [a]) = listWord n p + a • unitWord n p.length := by
  funext i
  by_cases hi : i.val < p.length
  · have hn : i.val ≠ p.length := by omega
    simp [listWord, List.getElem?_append, hi, unitWord, hn]
  · have hpnone : p[i.val]? = none := List.getElem?_eq_none (by omega)
    by_cases he : i.val = p.length
    · simp [listWord, List.getElem?_append, hi, he, unitWord, hpnone]
    · have ha : [a][i.val - p.length]? = none := List.getElem?_eq_none (by simp; omega)
      simp [listWord, List.getElem?_append, hi, unitWord, he, hpnone, ha]

private theorem dot_listWord_append {n : ℕ} (p : List Bit) (a d : Bit) (x : Word n)
    (hp : p.length < n) :
    dot (listWord n (p ++ [a])) x = dot (listWord n p) x + a * x ⟨p.length, hp⟩ := by
  rw [listWord_append, dot_add_left]
  have he : dot (a • unitWord n p.length) x = a * dot (unitWord n p.length) x := by
    simp [dot, mul_assoc, Finset.mul_sum]
  rw [he]
  have hu : dot (unitWord n p.length) x = x ⟨p.length, hp⟩ := by
    exact dot_unitWord x hp
  rw [hu]

private theorem suffixZero_succ_iff {n : ℕ} (d : Word n) (j : ℕ) (hj : j < n) :
    suffixZero d j ↔ d ⟨j, hj⟩ = 0 ∧ suffixZero d (j + 1) := by
  constructor
  · intro h; exact ⟨h _ (by simp), fun i hi => h i (by omega)⟩
  · rintro ⟨hj0, h⟩ i hi
    by_cases hie : i.val = j
    · have he : i = ⟨j, hj⟩ := Fin.ext hie
      simpa only [he] using hj0
    · exact h i (by omega)

private theorem partialContribution_children {n : ℕ} (d : Word n) (p : List Bit) (hp : p.length < n) :
    partialContribution d (p ++ [0]) + partialContribution d (p ++ [1]) = 2 * partialContribution d p := by
  classical
  have h0 := dot_listWord_append p 0 0 d hp
  have h1 := dot_listWord_append p 1 0 d hp
  unfold partialContribution
  simp only [List.length_append, List.length_singleton, h0, h1, zero_mul, one_mul, add_zero]
  rw [suffixZero_succ_iff d p.length hp]
  by_cases hs : suffixZero d (p.length + 1)
  · rcases bit_zero_or_one (d ⟨p.length, hp⟩) with hd | hd
    · simp only [hs, hd, and_self, if_pos, add_zero, ite_true, true_and]
      split_ifs <;> norm_num
    · rcases bit_zero_or_one (dot (listWord n p) d) with hc | hc
      · simp only [hs, hd, hc, zero_add, one_ne_zero, and_false, false_and, ite_true, ite_false, CharTwo.add_self_eq_zero]
        norm_num
      · simp only [hs, hd, hc, one_ne_zero, and_false, false_and, ite_true, ite_false, CharTwo.add_self_eq_zero]
        norm_num
  · simp [hs]

private theorem fixedSuffix_spec {n : ℕ} (f : Affine n) (x : Word n) (j : ℕ) :
    (∀ e ∈ (fixedEquations f).drop j, equationHolds e x) ↔ suffixZero (differenceAt f x) j := by
  constructor
  · intro h i hi
    have hik : j + (i.val - j) < n := by omega
    have heq : (⟨j + (i.val - j), hik⟩ : Fin n) = i := by
      apply Fin.ext
      change j + (i.val - j) = i.val
      omega
    have hm : ((difference f).matrix i, f.offset i) ∈ (fixedEquations f).drop j := by
      apply List.mem_drop_iff_getElem.mpr
      refine ⟨i.val - j, ?_, ?_⟩
      · simp only [fixedEquations, List.length_ofFn]; omega
      · simp only [fixedEquations, List.getElem_ofFn]
        rw [heq]
    have hh := h _ hm
    rw [← difference_apply]
    change dot ((difference f).matrix i) x + f.offset i = 0
    exact CharTwo.add_eq_zero.mpr hh
  · intro h e he
    obtain ⟨k, hk, he⟩ := List.mem_drop_iff_getElem.mp he
    have hik : j + k < n := by simp only [fixedEquations, List.length_ofFn] at hk; omega
    have heq : e = ((difference f).matrix ⟨j + k, hik⟩, f.offset ⟨j + k, hik⟩) := by
      simpa only [fixedEquations, List.getElem_ofFn] using he.symm
    rw [heq]
    have hh := h ⟨j + k, hik⟩ (by simp)
    rw [← difference_apply] at hh
    change dot ((difference f).matrix ⟨j + k, hik⟩) x + f.offset ⟨j + k, hik⟩ = 0 at hh
    exact CharTwo.add_eq_zero.mp hh

private theorem affine_witness_count {n : ℕ} (f : Affine n) (G : Rows n) (E : List (Equation n)) :
    affineCount (E ++ collisionEquations f G) - affineCount (E ++ fixedEquations f) =
      ∑ x : Word n, if (∀ e ∈ E, equationHolds e x) ∧ differenceAt f x ≠ 0 ∧
        syndrome G (differenceAt f x) = G.map (fun _ => 0) then 1 else 0 := by
  classical
  have hpoint (x : Word n) : witnessesAt [f] G x =
      if differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0) then 1 else 0 := by
    unfold witnessesAt
    by_cases hw : differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
    · rw [List.filter_cons, decide_eq_true hw, if_pos hw]
      rfl
    · rw [List.filter_cons, decide_eq_false hw, if_neg hw]
      rfl
  have hh := witnessCount_correct [f] G E
  simp only [witnessCount, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hh
  change _ = ∑ x ∈ affineSet E, witnessesAt [f] G x at hh
  simp_rw [hpoint] at hh
  simp only [affineSet, Finset.sum_filter] at hh
  simpa only [ite_and] using hh

private theorem twiceExpectation_singleton {n : ℕ} (f : Affine n) (G : Rows n) (p : List Bit) :
    twiceExpectation [f] G p =
      ∑ x : Word n, if differenceAt f x ≠ 0 ∧
        syndrome G (differenceAt f x) = G.map (fun _ => 0)
        then partialContribution (differenceAt f x) p else 0 := by
  classical
  unfold twiceExpectation witnessCount zeroSuffixCount zeroPrefixCount
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [affine_witness_count f G [], affine_witness_count f G ((fixedEquations f).drop p.length),
    affine_witness_count f G ((fixedEquations f).drop p.length ++ [pullZero (difference f) (listWord n p)])]
  simp only [List.not_mem_nil, forall_false, implies_true, List.forall_mem_append,
    List.forall_mem_singleton, fixedSuffix_spec, pullZero_spec, difference_apply, true_and]
  push_cast
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  unfold partialContribution
  split_ifs <;> simp_all <;> omega

private theorem twiceExpectation_cons {n : ℕ} (f : Affine n) (F : Family n) (G : Rows n) (p : List Bit) :
    twiceExpectation (f :: F) G p = twiceExpectation [f] G p + twiceExpectation F G p := by
  unfold twiceExpectation witnessCount zeroSuffixCount zeroPrefixCount
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add]
  ring

 theorem twiceExpectation_children {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit) (hp : p.length < n) :
    twiceExpectation F G (p ++ [0]) + twiceExpectation F G (p ++ [1]) = 2 * twiceExpectation F G p := by
  classical
  induction F with
  | nil => simp [twiceExpectation, witnessCount, zeroSuffixCount, zeroPrefixCount]
  | cons f F ih =>
    rw [twiceExpectation_cons f F G (p ++ [0]), twiceExpectation_cons f F G (p ++ [1]),
      twiceExpectation_cons f F G p]
    simp_rw [twiceExpectation_singleton]
    rw [add_add_add_comm, ih, ← Finset.sum_add_distrib, mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs with h
    · exact partialContribution_children _ p hp
    · ring

private theorem witnessSum_singleton {n : ℕ} (f : Affine n) (G : Rows n) (S : Finset (Word n)) :
    witnessSum [f] G S = ∑ x ∈ S, if differenceAt f x ≠ 0 ∧
      syndrome G (differenceAt f x) = G.map (fun _ => 0) then 1 else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  unfold witnessesAt
  by_cases hw : differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
  · rw [List.filter_cons, decide_eq_true hw, if_pos hw]
    rfl
  · rw [List.filter_cons, decide_eq_false hw, if_neg hw]
    rfl

private theorem witnessSum_cons {n : ℕ} (f : Affine n) (F : Family n) (G : Rows n) (S : Finset (Word n)) :
    witnessSum (f :: F) G S = witnessSum [f] G S + witnessSum F G S := by
  classical
  unfold witnessSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  unfold witnessesAt
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp [Nat.add_comm]

 theorem twiceExpectation_empty {n : ℕ} (F : Family n) (G : Rows n) :
    twiceExpectation F G [] = (witnessSum F G Finset.univ : ℤ) := by
  classical
  induction F with
  | nil => simp [twiceExpectation, witnessCount, zeroSuffixCount, zeroPrefixCount, witnessSum, witnessesAt]
  | cons f F ih =>
    have hsingle : twiceExpectation [f] G [] = (witnessSum [f] G Finset.univ : ℤ) := by
      rw [twiceExpectation_singleton, witnessSum_singleton]
      push_cast
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hw : differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
      · rw [if_pos hw, if_pos hw]
        have hs : ¬ suffixZero (differenceAt f x) 0 := by
          intro h
          apply hw.1
          funext i
          exact h i (by omega)
        simp only [partialContribution, List.length_nil, if_neg hs]
      · rw [if_neg hw, if_neg hw]
    rw [twiceExpectation_cons f F G [], hsingle, ih,
      witnessSum_cons f F G Finset.univ, Nat.cast_add]

 theorem twiceExpectation_complete {n : ℕ} (F : Family n) (G : Rows n) (h : Word n) :
    twiceExpectation F G (wordList h) = (2 * witnessSum F (G ++ [h]) Finset.univ : ℤ) := by
  classical
  induction F with
  | nil => simp [twiceExpectation, witnessCount, zeroSuffixCount, zeroPrefixCount, witnessSum, witnessesAt]
  | cons f F ih =>
    have hsingle : twiceExpectation [f] G (wordList h) =
        (2 * witnessSum [f] (G ++ [h]) Finset.univ : ℤ) := by
      rw [twiceExpectation_singleton, witnessSum_singleton]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hs : suffixZero (differenceAt f x) (wordList h).length := by
        intro i hi
        simp only [wordList_length] at hi
        omega
      simp only [partialContribution, if_pos hs, listWord_wordList, syndrome_append_zero]
      by_cases hw : differenceAt f x ≠ 0 ∧ syndrome G (differenceAt f x) = G.map (fun _ => 0)
      <;> by_cases hd : dot h (differenceAt f x) = 0
      <;> simp [hw, hd] <;> tauto
    rw [twiceExpectation_cons f F G (wordList h), hsingle, ih,
      witnessSum_cons f F (G ++ [h]) Finset.univ, Nat.cast_add]
    ring

 theorem chooseRowPrefix_length {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit) :
    (chooseRowPrefix F G k p).length = p.length + k := by
  induction k generalizing p with
  | zero => simp [chooseRowPrefix]
  | succ k ih => simp only [chooseRowPrefix]; rw [ih]; simp; omega

 theorem chooseRowPrefix_bound {n : ℕ} (F : Family n) (G : Rows n) (k : ℕ) (p : List Bit)
    (hlen : p.length + k ≤ n) :
    twiceExpectation F G (chooseRowPrefix F G k p) ≤ twiceExpectation F G p := by
  induction k generalizing p with
  | zero => simp [chooseRowPrefix]
  | succ k ih =>
    have hchild := twiceExpectation_children F G p (by omega)
    simp only [chooseRowPrefix]
    split_ifs with h
    · exact (ih (p ++ [0]) (by simp; omega)).trans (by omega)
    · exact (ih (p ++ [1]) (by simp; omega)).trans (by omega)

 theorem chooseRow_halves {n : ℕ} (F : Family n) (G : Rows n) :
    2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ := by
  have hlen : (chooseRowPrefix F G n []).length = n := by rw [chooseRowPrefix_length]; simp
  have hlist : wordList (chooseRow F G) = chooseRowPrefix F G n [] := wordList_listWord _ hlen
  have hb := chooseRowPrefix_bound F G n [] (by simp)
  rw [← hlist, twiceExpectation_complete, twiceExpectation_empty] at hb
  exact_mod_cast hb

end EditGV897.Main


namespace EditGV897.Main

 theorem rowCompletions_prefix {n : ℕ} (p : List Bit) :
    rowCompletions n p = prefixCoset ([] : Rows n) [] p := by
  classical
  ext h
  simp [rowCompletions, prefixCoset, coset, syndrome]

 theorem rowCompletions_card {n : ℕ} (p : List Bit) (hp : p.length ≤ n) :
    (rowCompletions n p).card = 2 ^ (n - p.length) := by
  classical
  let extend : Word (n - p.length) → Word n := fun u => listWord n (p ++ wordList u)
  have hlen (u : Word (n - p.length)) : (p ++ wordList u).length = n := by simp; omega
  have hext (u : Word (n - p.length)) : wordList (extend u) = p ++ wordList u :=
    wordList_listWord _ (hlen u)
  have hinj : Function.Injective extend := by
    intro u v he
    have hh := congrArg (fun w : Word n => (wordList w).drop p.length) he
    simp only [hext, List.drop_left] at hh
    exact List.ofFn_injective hh
  have hset : (Finset.univ.image extend) = rowCompletions n p := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [rowCompletions, Finset.mem_filter, Finset.mem_univ, true_and, hext]
      simp
    · intro hx
      have hprefix : (wordList x).take p.length = p := (Finset.mem_filter.mp hx).2
      let u : Word (n - p.length) := listWord (n - p.length) ((wordList x).drop p.length)
      have hu : wordList u = (wordList x).drop p.length :=
        wordList_listWord _ (by simp)
      apply Finset.mem_image.mpr
      refine ⟨u, Finset.mem_univ _, ?_⟩
      apply List.ofFn_injective
      change wordList (extend u) = wordList x
      rw [hext, hu]
      calc
        p ++ (wordList x).drop p.length =
            (wordList x).take p.length ++ (wordList x).drop p.length :=
          congrArg (fun q : List Bit => q ++ (wordList x).drop p.length) hprefix.symm
        _ = wordList x := by rw [List.take_append_drop]
  rw [← hset, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp [Word, DeletionHash.MixedEdit.Word, Bit, ZMod.card]

 theorem twiceExpectation_completion_sum {n : ℕ} (F : Family n) (G : Rows n)
    (k : ℕ) (p : List Bit) (hlen : p.length + k = n) :
    ∑ h ∈ rowCompletions n p, (2 * witnessSum F (G ++ [h]) Finset.univ : ℤ) =
      2 ^ k * twiceExpectation F G p := by
  classical
  induction k generalizing p with
  | zero =>
    have hp : p.length = n := by omega
    have hset : rowCompletions n p = {listWord n p} := by
      rw [rowCompletions_prefix, prefixCoset_leaf _ _ _ hp]
      simp [syndrome]
    rw [hset, Finset.sum_singleton, ← twiceExpectation_complete, wordList_listWord _ hp]
    simp
  | succ k ih =>
    have hp : p.length < n := by omega
    obtain ⟨hu, hd⟩ := prefixCoset_children ([] : Rows n) [] p hp
    simp only [← rowCompletions_prefix] at hu hd
    rw [hu, Finset.sum_union hd,
      ih (p ++ [0]) (by simp only [List.length_append, List.length_singleton]; omega),
      ih (p ++ [1]) (by simp only [List.length_append, List.length_singleton]; omega)]
    calc
      _ = 2 ^ k * (twiceExpectation F G (p ++ [0]) + twiceExpectation F G (p ++ [1])) := by ring
      _ = _ := by rw [twiceExpectation_children F G p hp, pow_succ]; ring

 theorem twiceExpectation_correct {n : ℕ} (F : Family n) (G : Rows n) (p : List Bit)
    (hp : p.length ≤ n) : (twiceExpectation F G p : ℚ) = 2 * expectation F G p := by
  have hz := twiceExpectation_completion_sum F G (n - p.length) p (by omega)
  have hq : 2 * (∑ h ∈ rowCompletions n p, (witnessSum F (G ++ [h]) Finset.univ : ℚ)) =
      (2 ^ (n - p.length) : ℚ) * (twiceExpectation F G p : ℚ) := by
    have hh : 2 * (∑ h ∈ rowCompletions n p, (witnessSum F (G ++ [h]) Finset.univ : ℤ)) =
        (2 ^ (n - p.length) : ℤ) * twiceExpectation F G p := by
      simpa only [Finset.mul_sum] using hz
    exact_mod_cast hh
  unfold expectation
  rw [rowCompletions_card p hp]
  push_cast
  field_simp
  nlinarith [hq]

end EditGV897.Main

open EditGV897.Main

theorem solution :
    (∀ (n : ℕ) (E : List (Equation n)), affineCount E = (affineSet E).card) ∧
    (∀ (n t : ℕ) (F : Family n) (G : Rows n),
      1 ≤ t → EditFamily t F → G.length ≤ n →
      (∀ E : List (Equation n), witnessCount F G E = witnessSum F G (affineSet E)) ∧
      (∀ p : List Bit, p.length ≤ n → (twiceExpectation F G p : ℚ) = 2 * expectation F G p) ∧
      2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ) := by
  refine ⟨affine_count_correct, ?_⟩
  intro n t F G ht hF hG
  exact ⟨witness_count_correct n F G, twiceExpectation_correct F G, chooseRow_halves F G⟩
