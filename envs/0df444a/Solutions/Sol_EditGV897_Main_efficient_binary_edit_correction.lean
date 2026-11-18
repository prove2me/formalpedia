-- Prove2me | solution 1 for EditGV897.Main.efficient_binary_edit_correction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T01:58:34.373206+00:00
-- url     : https://prove2.me/submissions/5054617a-00cc-4d87-a6f5-02736dc0d12e

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_encoding_recovering_messages

import Theorems.Thm_EditGV897_Main_setup_certificates

import Theorems.Thm_EditGV897_Main_main_programs


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


namespace DeletionHash.MixedEdit

 theorem applyEdit_reverse {α : Type*} (b : ℕ) (x : List α) (e : Edit α)
    (he : ValidEdit b x e) :
    ∃ e' : Edit α, ValidEdit b (applyEdit e x) e' ∧ applyEdit e' (applyEdit e x) = x := by
  let a := x.take e.position
  let z := (x.drop e.position).take e.removed
  let c := x.drop (e.position + e.removed)
  have hk : e.position ≤ x.length := by have := he.1; omega
  have ha : a.length = e.position := by simp [a, List.length_take, Nat.min_eq_left hk]
  have hz : z.length = e.removed := by
    simp only [z, List.length_take, List.length_drop]
    have := he.1
    omega
  have hx : a ++ z ++ c = x := by
    dsimp [a, z, c]
    rw [List.append_assoc, ← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hy : applyEdit e x = a ++ e.replacement ++ c := rfl
  refine ⟨⟨e.position, e.replacement.length, z⟩, ?_, ?_⟩
  · unfold ValidEdit
    simp only
    refine ⟨?_, he.2.2.1, ?_, ?_⟩
    · rw [hy]
      simp only [List.length_append, ha]
      omega
    · rw [hz]
      exact he.2.1
    · have hw : window e.replacement.length (applyEdit e x) e.position = e.replacement := by
        rw [hy]
        dsimp [window]
        rw [List.append_assoc, ← ha]
        simp
      rw [hw]
      exact Ne.symm he.2.2.2
  · change (applyEdit e x).take e.position ++ z ++
      (applyEdit e x).drop (e.position + e.replacement.length) = x
    have ht : (a ++ e.replacement ++ c).take a.length = a := by
      rw [List.append_assoc]
      simp
    have hc : (a ++ e.replacement ++ c).drop (a.length + e.replacement.length) = c := by
      rw [← List.length_append]
      simp
    rw [hy, ← ha, ht, hc]
    exact hx

 theorem target_append {α : Type*} (x : List α) (r s : List (Edit α)) :
    target x (r ++ s) = target (target x r) s := by
  exact List.foldl_append

 theorem validRecord_append {α : Type*} (b : ℕ) (x : List α) (r s : List (Edit α)) :
    ValidRecord b x (r ++ s) ↔ ValidRecord b x r ∧ ValidRecord b (target x r) s := by
  induction r generalizing x with
  | nil => simp [ValidRecord, target]
  | cons e r ih =>
    simp only [List.cons_append, ValidRecord, target, List.foldl_cons, ih]
    tauto

 theorem reaches_trans {α : Type*} {b s t : ℕ} {x y z : List α}
    (hxy : Reaches b s x y) (hyz : Reaches b t y z) : Reaches b (s + t) x z := by
  obtain ⟨r, hr, hvr, htr⟩ := hxy
  obtain ⟨q, hq, hvq, htq⟩ := hyz
  refine ⟨r ++ q, ?_, ?_, ?_⟩
  · simp only [List.length_append]; omega
  · rw [validRecord_append, htr]
    exact ⟨hvr, hvq⟩
  · rw [target_append, htr, htq]

 theorem reaches_symm {α : Type*} {b t : ℕ} {x y : List α} (h : Reaches b t x y) :
    Reaches b t y x := by
  obtain ⟨r, hr, hvr, rfl⟩ := h
  suffices hall : ∀ (r : List (Edit α)) (x : List α), ValidRecord b x r →
      Reaches b r.length (target x r) x by
    obtain ⟨q, hq, hvq, htq⟩ := hall r x hvr
    exact ⟨q, by omega, hvq, htq⟩
  intro r
  induction r with
  | nil => intro x h; exact ⟨[], by simp, trivial, rfl⟩
  | cons e r ih =>
    intro x h
    obtain ⟨e', he', he'x⟩ := applyEdit_reverse b x e h.1
    have hback : Reaches b 1 (applyEdit e x) x :=
      ⟨[e'], by simp, ⟨he', trivial⟩, he'x⟩
    have htail := ih (applyEdit e x) h.2
    simpa only [List.length_cons, Nat.add_comm _ 1, target, List.foldl_cons] using
      reaches_trans htail hback

end DeletionHash.MixedEdit


namespace EditGV897.Main

open DeletionHash.MixedEdit

 theorem legal_insert (x : List Bit) (k : ℕ) (a : Bit) (hk : k ≤ x.length) :
    PositionedOp.insert k a ∈ legalOps x.length := by
  have ha := bit_zero_or_one a
  rcases ha with rfl | rfl <;>
    simp [legalOps, List.mem_flatMap, List.mem_range, Nat.lt_succ_iff, hk]

 theorem legal_delete (x : List Bit) (k : ℕ) (hk : k < x.length) :
    PositionedOp.delete k ∈ legalOps x.length := by
  simp [legalOps, List.mem_map, List.mem_range, hk]

 theorem legal_toggle (x : List Bit) (k : ℕ) (hk : k < x.length) :
    PositionedOp.toggle k ∈ legalOps x.length := by
  simp [legalOps, List.mem_map, List.mem_range, hk]

 theorem validEdit_to_bitStep (x : List Bit) (e : Edit Bit) (he : ValidEdit 1 x e) :
    ∃ op ∈ legalOps x.length, bitStep x op = applyEdit e x := by
  rcases e with ⟨k, r, q⟩
  change k + r ≤ x.length ∧ r ≤ 1 ∧ q.length ≤ 1 ∧ window r x k ≠ q at he
  obtain ⟨hkr, hr, hq, hdiff⟩ := he
  have hr' : r = 0 ∨ r = 1 := by omega
  have hq' : q = [] ∨ ∃ a, q = [a] := by
    cases q with
    | nil => exact Or.inl rfl
    | cons a q =>
      have : q = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hq; omega)
      subst q
      exact Or.inr ⟨a, rfl⟩
  rcases hr' with rfl | rfl <;> rcases hq' with rfl | ⟨a, rfl⟩
  · simp [window] at hdiff
  · exact ⟨.insert k a, legal_insert x k a (by omega), by simp [bitStep, applyEdit]⟩
  · exact ⟨.delete k, legal_delete x k (by omega), by simp [bitStep, applyEdit]⟩
  · have hk : k < x.length := by omega
    have hdrop : x.drop k = x[k] :: x.drop (k + 1) := by
      exact List.drop_eq_getElem_cons hk
    have hab : x[k] ≠ a := by
      change (x.drop k).take 1 ≠ [a] at hdiff
      rw [hdrop] at hdiff
      simp only [List.take_succ_cons, List.take_zero] at hdiff
      exact fun h => hdiff (congrArg (fun z => [z]) h)
    have htoggle : x[k] + 1 = a := by
      have hx := bit_zero_or_one x[k]
      have ha := bit_zero_or_one a
      rcases hx with hx | hx <;> rcases ha with rfl | rfl <;>
        rw [hx] at hab ⊢ <;> first
        | exact (hab rfl).elim
        | exact zero_add 1
        | exact CharTwo.add_self_eq_zero (1 : Bit)
    refine ⟨.toggle k, legal_toggle x k hk, ?_⟩
    change x.take k ++ ((x.drop k).take 1).map (fun a => a + 1) ++ x.drop (k + 1) =
      x.take k ++ [a] ++ x.drop (k + 1)
    rw [hdrop]
    simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, htoggle]

 theorem mem_candidates_of_reaches {t : ℕ} {x y : List Bit} (h : Reaches 1 t x y) :
    y ∈ candidates t x := by
  obtain ⟨r, hr, hvr, rfl⟩ := h
  induction t generalizing x r with
  | zero =>
    have : r = [] := List.length_eq_zero_iff.mp (by omega)
    subst r
    simp [target, candidates]
  | succ t ih =>
    cases r with
    | nil => simp [target, candidates]
    | cons e r =>
      obtain ⟨op, hop, heq⟩ := validEdit_to_bitStep x e hvr.1
      have hm := ih (x := applyEdit e x) (r := r) (by simpa using hr) hvr.2
      simp only [target, List.foldl_cons] at hm ⊢
      simp only [candidates, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨op, hop, by simpa [heq] using hm⟩

theorem bitStep_valid (x : List Bit) (op : PositionedOp) (hop : op ∈ legalOps x.length) :
    ∃ e : Edit Bit, ValidEdit 1 x e ∧ applyEdit e x = bitStep x op := by
  cases op with
  | insert k a =>
    have hk : k ≤ x.length := by
      simp only [legalOps, List.mem_append, List.mem_flatMap, List.mem_range,
        List.mem_cons, List.not_mem_nil, or_false, PositionedOp.insert.injEq,
        List.mem_map, reduceCtorEq, false_and, and_false, exists_false, or_false] at hop
      obtain ⟨j, hj, h⟩ := hop
      rcases h with h | h <;> obtain ⟨rfl, _⟩ := h <;> omega
    refine ⟨⟨k, 0, [a]⟩, ?_, rfl⟩
    simp [ValidEdit, window, hk]
  | delete k =>
    have hk : k < x.length := by
      simpa [legalOps, List.mem_map, List.mem_flatMap] using hop
    refine ⟨⟨k, 1, []⟩, ?_, ?_⟩
    · have hd := List.drop_eq_getElem_cons hk
      change k + 1 ≤ x.length ∧ 1 ≤ 1 ∧ 0 ≤ 1 ∧ (x.drop k).take 1 ≠ []
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [hd]
      simp
      exact hk
    · simp [applyEdit, bitStep]
  | toggle k =>
    have hk : k < x.length := by
      simpa [legalOps, List.mem_map, List.mem_flatMap] using hop
    have hd := List.drop_eq_getElem_cons hk
    refine ⟨⟨k, 1, [x[k] + 1]⟩, ?_, ?_⟩
    · change k + 1 ≤ x.length ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧ (x.drop k).take 1 ≠ [x[k] + 1]
      refine ⟨by omega, by omega, by omega, ?_⟩
      rw [hd]
      simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
      intro heq
      have heq' := List.singleton_inj.mp heq
      have : (1 : Bit) = 0 := add_left_cancel (show x[k] + 1 = x[k] + 0 by simpa using heq'.symm)
      exact one_ne_zero this
    · change x.take k ++ [x[k] + 1] ++ x.drop (k + 1) =
        x.take k ++ ((x.drop k).take 1).map (fun a => a + 1) ++ x.drop (k + 1)
      rw [hd]
      rfl

theorem reaches_of_mem_candidates {t : ℕ} {x y : List Bit} (h : y ∈ candidates t x) :
    Reaches 1 t x y := by
  induction t generalizing x y with
  | zero =>
    simp only [candidates, List.mem_singleton] at h
    subst y
    exact ⟨[], by simp, trivial, rfl⟩
  | succ t ih =>
    simp only [candidates, List.mem_cons, List.mem_flatMap] at h
    rcases h with rfl | ⟨op, hop, hm⟩
    · exact ⟨[], by simp, trivial, rfl⟩
    · obtain ⟨e, he, heq⟩ := bitStep_valid x op hop
      obtain ⟨r, hr, hvr, htr⟩ := ih hm
      refine ⟨e :: r, by simp only [List.length_cons]; omega, ?_, ?_⟩
      · exact ⟨he, by simpa only [heq] using hvr⟩
      · simpa only [target, List.foldl_cons, heq] using htr

theorem reaches_length_le {t : ℕ} {x y : List Bit} (h : Reaches 1 t x y) :
    y.length ≤ x.length + t := by
  obtain ⟨r, hr, hvr, rfl⟩ := h
  suffices hall : ∀ (r : List (Edit Bit)) (x : List Bit), ValidRecord 1 x r →
      (target x r).length ≤ x.length + r.length by
    have := hall r x hvr
    omega
  intro r
  induction r with
  | nil => intro x h; simp [target]
  | cons e r ih =>
    intro x h
    have hs : (applyEdit e x).length ≤ x.length + 1 := by
      obtain ⟨hpos, hrem, hrepl, hneq⟩ := h.1
      simp only [applyEdit, List.length_append, List.length_take, List.length_drop]
      omega
    have ht := ih (applyEdit e x) h.2
    simp only [target, List.foldl_cons, List.length_cons] at ht ⊢
    omega

end EditGV897.Main


namespace EditGV897.Main

open DeletionHash.MixedEdit

 theorem decodeList_correct {n t : ℕ} (P : Parameters n) (x : Word n)
    (hs : syndrome P.rows x = P.beta) (hsep : Separated t P.rows x)
    (y : List Bit) (hy : Reaches 1 t (wordList x) y) :
    decodeList t P y = some (inverseList (canonicalFamily t n) P (wordList x)) := by
  classical
  have hlen : y.length ≤ n + t := by
    simpa using reaches_length_le hy
  have hmem : wordList x ∈ candidates t y := mem_candidates_of_reaches (reaches_symm hy)
  let pred := fun z : List Bit => z.length == n && decide (syndrome P.rows (listWord n z) = P.beta)
  have hpred : pred (wordList x) = true := by
    simp [pred, hs]
  have hfind : (candidates t y).find? pred = some (wordList x) := by
    have hex : ∃ z ∈ candidates t y, pred z = true := ⟨wordList x, hmem, hpred⟩
    have hsome := List.find?_isSome.mpr hex
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hsome
    have hzm : z ∈ candidates t y := List.mem_of_find?_eq_some hz
    have hzp : pred z = true := List.find?_some hz
    have hparts : z.length = n ∧ syndrome P.rows (listWord n z) = P.beta := by
      simpa only [pred, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using hzp
    have hzl : z.length = n := by
      exact hparts.1
    have hzsy : syndrome P.rows (listWord n z) = P.beta := by
      exact hparts.2
    have hzy : Reaches 1 t (wordList (listWord n z)) y := by
      rw [wordList_listWord z hzl]
      exact reaches_symm (reaches_of_mem_candidates hzm)
    have hzx : listWord n z = x := by
      by_contra hne
      exact hsep _ (Ne.symm hne) ⟨y, hy, hzy⟩ (hs.trans hzsy.symm)
    have hzeq : z = wordList x := by
      rw [← hzx, wordList_listWord z hzl]
    simpa only [hzeq] using hz
  unfold decodeList
  rw [if_neg (by omega)]
  change ((candidates t y).find? pred).map _ = _
  rw [hfind]
  rfl

end EditGV897.Main


namespace EditGV897.Main

 theorem codeImage_card {n : ℕ} (F : Family n) (P : Parameters n)
    (hinj : Function.Injective (encodeWord F P)) :
    (codeImage F P).card = 2 ^ messageLength P := by
  classical
  rw [codeImage, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp [Word, DeletionHash.MixedEdit.Word, Bit, ZMod.card]

 theorem logTwo_two_pow (k : ℕ) : logTwo ((2 : ℝ) ^ k) = k := by
  have hlog : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  unfold logTwo
  push_cast
  rw [Real.log_pow]
  field_simp

 theorem codeImage_redundancy {n : ℕ} (F : Family n) (P : Parameters n)
    (hinj : Function.Injective (encodeWord F P)) (hb : P.rows.length < n) :
    (n : ℝ) - logTwo (codeImage F P).card = (P.rows.length + 1 : ℕ) := by
  rw [codeImage_card F P hinj]
  push_cast
  rw [logTwo_two_pow]
  have hnat : n = messageLength P + (P.rows.length + 1) := by
    unfold messageLength
    omega
  have hreal : (n : ℝ) = (messageLength P : ℝ) + (P.rows.length + 1 : ℕ) := by
    exact_mod_cast hnat
  push_cast at hreal
  linarith

 theorem codeImage_corrects {n t : ℕ} (F : Family n) (P : Parameters n)
    (hsep : ∀ u : Word (messageLength P), Separated t P.rows (encodeWord F P u))
    (hsy : ∀ u : Word (messageLength P), syndrome P.rows (encodeWord F P u) = P.beta) :
    DeletionHash.MixedEdit.Corrects 1 t (codeImage F P) := by
  classical
  intro x hx y hy hxy hc
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hy
  exact hsep u _ hxy hc ((hsy u).trans (hsy v).symm)

end EditGV897.Main


open EditGV897.Main

theorem solution (t : ℕ) (ht : 1 ≤ t) :
    ∃ (constructor encoder decoder : Program) (C : ℝ) (A d N : ℕ),
      0 < C ∧ C = redundancyConstant t ∧ 0 < A ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        let K := messageLength P
        let code := codeImage F P
        EditFamily t F ∧ F.length ≤ familyCoefficient t * n ^ (2 * t) ∧
        P.rows.length = checkRows F.length ∧ P.rows.length < n ∧ FullRowRank P.rows ∧
        P.beta.length = P.rows.length ∧
        witnessSum F P.rows Finset.univ ≤ F.length * 2 ^ (n - P.rows.length) ∧
        witnessSum F P.rows Finset.univ ≤ 2 ^ (n - 1) ∧
        (2 ^ K : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) ∧
        (parametersCode P).length ≤ polyBudget A d n ∧
        Runs constructor (unary n) (parametersCode P) (polyBudget A d n) ∧
        Function.Injective (encodeWord F P) ∧ code.card = 2 ^ K ∧
        (n : ℝ) - logTwo code.card = (P.rows.length + 1 : ℕ) ∧
        (n : ℝ) - logTwo code.card ≤ (2 * t : ℕ) * logTwo n + C ∧
        DeletionHash.MixedEdit.Corrects 1 t code ∧
        (∀ u : Word K,
          let x := encodeWord F P u
          (encodeList F P u).length = n ∧ encodeList F P u = wordList x ∧
          syndrome P.rows x = P.beta ∧ Separated t P.rows x ∧
          inverseList F P (wordList x) = wordList u ∧
          Runs encoder (editEncoderInput P u) (wordCode x) (polyBudget A d n) ∧
          (∀ y : List Bit,
            DeletionHash.MixedEdit.Reaches 1 t (wordList x) y →
            decodeList t P y = some (wordList u) ∧
            Runs decoder (editDecoderInput P y) (wordCode u) (polyBudget A d n))) := by
  obtain ⟨hC, N, hN, hsetup⟩ := setup_certificates t ht
  obtain ⟨constructor, encoder, decoder, A, d, hA, hprogram⟩ := main_programs t ht
  obtain ⟨_, _, _, _, _, hindex⟩ := encoding_recovering_messages
  refine ⟨constructor, encoder, decoder, redundancyConstant t, A, d, N,
    hC, rfl, hA, hN, ?_⟩
  intro n hn
  obtain ⟨hF, hsize, hrows, hsmall, hrank, hbeta, hw1, hw2, hroot, hred⟩ := hsetup n hn
  have hsem := hindex n t (canonicalFamily t n) (setup t n) ht hF hrows hsmall hrank hbeta hroot
  obtain ⟨hparam, hconstructor, hencoder, hdecoder⟩ := hprogram n (le_trans hN hn)
  have hcard := codeImage_card (canonicalFamily t n) (setup t n) hsem.1
  have hredEq := codeImage_redundancy (canonicalFamily t n) (setup t n) hsem.1 hsmall
  have hcorrect := codeImage_corrects (canonicalFamily t n) (setup t n)
    (fun u => (hsem.2 u).2.2.2.1) (fun u => (hsem.2 u).2.2.1)
  refine ⟨hF, hsize, hrows, hsmall, hrank, hbeta, hw1, hw2, hroot,
    hparam, hconstructor, hsem.1, hcard, hredEq, ?_, hcorrect, ?_⟩
  · rw [hredEq]
    exact hred
  · intro u
    have hu := hsem.2 u
    refine ⟨hu.2.1, hu.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.2.1, hencoder u, ?_⟩
    intro y hy
    have hdecode := decodeList_correct (setup t n) (encodeWord (canonicalFamily t n) (setup t n) u)
      hu.2.2.1 hu.2.2.2.1 y hy
    rw [hu.2.2.2.2.2.1] at hdecode
    refine ⟨hdecode, ?_⟩
    have hlen : y.length ≤ n + t := by simpa using reaches_length_le hy
    have hr := hdecoder y hlen
    simpa only [hdecode, Option.getD_some, wordCode] using hr