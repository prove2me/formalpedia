-- Prove2me | solution 1 for EditGV897.Main.setup_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:05:00.445305+00:00
-- url     : https://prove2.me/submissions/06c859a0-0a3c-4400-b1a3-3a86fb664747

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_matrix_certificates

import Theorems.Thm_EditGV897_Main_choosing_syndrome


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

private def evalSymbols {n : ℕ} (s : List (Equation n)) (x : Word n) : List Bit :=
  s.map (fun e => dot e.1 x + e.2)

private theorem evalSymbols_length {n : ℕ} (s : List (Equation n)) (x : Word n) :
    (evalSymbols s x).length = s.length := by simp [evalSymbols]

private theorem evalSymbols_step {n : ℕ} (s : List (Equation n)) (x : Word n) (op : PositionedOp) :
    evalSymbols (symbolicStep s op) x = bitStep (evalSymbols s x) op := by
  cases op with
  | insert k a => simp [evalSymbols, symbolicStep, bitStep, dot]
  | delete k => simp [evalSymbols, symbolicStep, bitStep]
  | toggle k =>
    simp [evalSymbols, symbolicStep, bitStep, List.map_map, Function.comp_def, add_assoc]

private theorem symbolicPaths_covers {n : ℕ} (s : List (Equation n)) (x : Word n)
    (r : ℕ) (y : List Bit) (hy : y ∈ candidates r (evalSymbols s x)) :
    ∃ s' ∈ symbolicPaths r s, evalSymbols s' x = y := by
  induction r generalizing s y with
  | zero =>
    simp only [candidates, List.mem_singleton] at hy
    exact ⟨s, by simp [symbolicPaths], hy.symm⟩
  | succ r ih =>
    simp only [candidates, List.mem_cons, List.mem_flatMap] at hy
    rcases hy with rfl | ⟨op, hop, hy⟩
    · exact ⟨s, by simp [symbolicPaths], rfl⟩
    · rw [← evalSymbols_step] at hy
      obtain ⟨s', hs', heq⟩ := ih _ _ hy
      refine ⟨s', ?_, heq⟩
      simp only [symbolicPaths, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨op, by simpa only [evalSymbols_length] using hop, hs'⟩

private theorem evalSymbols_start {n : ℕ} (x : Word n) :
    evalSymbols (List.ofFn (fun i : Fin n => (unitWord n i.val, (0 : Bit)))) x = wordList x := by
  simp only [evalSymbols, List.map_ofFn, wordList, DeletionHash.MixedEdit.letters]
  congr 1
  funext i
  simp [dot_unitWord x i.isLt]

 theorem canonicalFamily_coverage (t n : ℕ) (x y : Word n)
    (hc : DeletionHash.MixedEdit.Confusable 1 t (wordList x) (wordList y)) :
    ∃ f ∈ canonicalFamily t n, f.apply x = y := by
  obtain ⟨z, hxz, hyz⟩ := hc
  have hxy := DeletionHash.MixedEdit.reaches_trans hxz (DeletionHash.MixedEdit.reaches_symm hyz)
  have hm : wordList y ∈ candidates (2 * t) (wordList x) := by
    simpa only [two_mul] using mem_candidates_of_reaches hxy
  rw [← evalSymbols_start x] at hm
  obtain ⟨s, hs, he⟩ := symbolicPaths_covers _ x (2 * t) _ hm
  have hlen : s.length = n := by
    have := congrArg List.length he
    simpa only [evalSymbols_length, wordList_length] using this
  let f : Affine n :=
    { matrix := fun i => (s[i.val]?.getD ((0, 0) : Equation n)).1
      offset := fun i => (s[i.val]?.getD ((0, 0) : Equation n)).2 }
  refine ⟨f, ?_, ?_⟩
  · unfold canonicalFamily
    apply List.mem_map.mpr
    exact ⟨s, List.mem_filter.mpr ⟨hs, by simp [hlen]⟩, rfl⟩
  · funext i
    have hei := congrArg (fun l : List Bit => l[i.val]?) he
    have hi : i.val < s.length := by simpa [hlen] using i.isLt
    simpa [Affine.apply, f, evalSymbols, wordList, DeletionHash.MixedEdit.letters, hi] using hei

private theorem symbolicPaths_self {n : ℕ} (r : ℕ) (s : List (Equation n)) :
    s ∈ symbolicPaths r s := by
  cases r <;> simp [symbolicPaths]

theorem canonicalFamily_editFamily (t n : ℕ) : EditFamily t (canonicalFamily t n) := by
  have hne : ∃ f, f ∈ canonicalFamily t n := by
    let start := List.ofFn (fun i : Fin n => (unitWord n i.val, (0 : Bit)))
    have hs : start ∈ (symbolicPaths (2 * t) start).filter (fun s => s.length == n) := by
      apply List.mem_filter.mpr
      exact ⟨symbolicPaths_self _ _, by simp [start]⟩
    unfold canonicalFamily
    exact ⟨_, List.mem_map.mpr ⟨start, hs, rfl⟩⟩
  have hnot : canonicalFamily t n ≠ [] := by
    intro h
    obtain ⟨f, hf⟩ := hne
    rw [h] at hf
    exact List.not_mem_nil hf
  refine ⟨by have := List.length_pos_iff.mpr hnot; omega, ?_, ?_⟩
  · intro x y hxy hc
    exact canonicalFamily_coverage t n x y hc
  · intro f hf
    exact ⟨f, hf, rfl, rfl⟩

private theorem legalOps_length (L : ℕ) : (legalOps L).length = 4 * L + 2 := by
  simp [legalOps, List.length_flatMap]
  omega

private theorem symbolicStep_length_le {n : ℕ} (s : List (Equation n)) (op : PositionedOp) :
    (symbolicStep s op).length ≤ s.length + 1 := by
  cases op <;> simp only [symbolicStep, List.length_append, List.length_singleton,
    List.length_take, List.length_drop, List.length_map] <;> omega

private theorem symbolicPaths_length_le {n : ℕ} (r bound D : ℕ) (s : List (Equation n))
    (hlen : s.length + r ≤ bound) (hD : 4 * bound + 2 ≤ D) :
    (symbolicPaths r s).length ≤ (r + 1) * D ^ r := by
  induction r generalizing s with
  | zero => simp [symbolicPaths]
  | succ r ih =>
    have hsum : ((legalOps s.length).map (fun op =>
        (symbolicPaths r (symbolicStep s op)).length)).sum ≤
        (legalOps s.length).length * ((r + 1) * D ^ r) := by
      calc
        _ ≤ ((legalOps s.length).map (fun _ => (r + 1) * D ^ r)).sum := by
          apply List.sum_le_sum
          intro op hop
          apply ih
          have hs := symbolicStep_length_le s op
          omega
        _ = _ := by simp [List.sum_replicate, Nat.mul_comm]
    have hops : (legalOps s.length).length ≤ D := by rw [legalOps_length]; omega
    have hpow : 1 ≤ D ^ (r + 1) := Nat.one_le_pow _ _ (by omega)
    simp only [symbolicPaths, List.length_cons, List.length_flatMap]
    calc
      _ ≤ (legalOps s.length).length * ((r + 1) * D ^ r) + 1 := by omega
      _ ≤ D * ((r + 1) * D ^ r) + 1 := by gcongr
      _ ≤ (r + 1 + 1) * D ^ (r + 1) := by rw [pow_succ] at hpow ⊢; nlinarith

theorem canonicalFamily_length_le (t n : ℕ) (hn : 1 ≤ n) :
    (canonicalFamily t n).length ≤ familyCoefficient t * n ^ (2 * t) := by
  have hD : 4 * (n + 2 * t) + 2 ≤ 8 * (t + 1) * n := by nlinarith
  have h := symbolicPaths_length_le (2 * t) (n + 2 * t) (8 * (t + 1) * n)
    (List.ofFn (fun i : Fin n => (unitWord n i.val, (0 : Bit)))) (by simp) hD
  have hf : (canonicalFamily t n).length ≤
      (2 * t + 1) * (8 * (t + 1) * n) ^ (2 * t) := by
    unfold canonicalFamily
    simp only [List.length_map]
    exact (List.length_filter_le _ _).trans h
  simpa only [familyCoefficient, mul_pow, mul_assoc] using hf

end EditGV897.Main


namespace EditGV897.Main

open Filter Asymptotics

 theorem redundancyConstant_pos (t : ℕ) : 0 < redundancyConstant t := by
  have hcoef : 1 ≤ familyCoefficient t := by
    have hp : 0 < familyCoefficient t := by unfold familyCoefficient; positivity
    omega
  have hlog : 0 ≤ logTwo (familyCoefficient t) := by
    change 0 ≤ Real.logb 2 (familyCoefficient t)
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hcoef)
  unfold redundancyConstant
  linarith

 theorem checkRows_redundancy_bound (t n M : ℕ) (hn : 1 ≤ n) (hM : 1 ≤ M)
    (hsize : M ≤ familyCoefficient t * n ^ (2 * t)) :
    (checkRows M + 1 : ℕ) ≤ (2 * t : ℕ) * logTwo n + redundancyConstant t := by
  have htwo : 1 < (2 : ℝ) := by norm_num
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcpos : 0 < (familyCoefficient t : ℝ) := by
    exact_mod_cast (show 0 < familyCoefficient t by unfold familyCoefficient; positivity)
  have hlognonneg : 0 ≤ Real.logb (2 : ℝ) (2 * M : ℕ) :=
    Real.logb_nonneg htwo (by norm_cast; omega)
  have hceil := Nat.ceil_lt_add_one hlognonneg
  have hclog : ⌈Real.logb (2 : ℝ) (2 * M : ℕ)⌉₊ = Nat.clog 2 (2 * M) := by
    simpa only [Nat.cast_ofNat] using Real.natCeil_logb_natCast 2 (2 * M)
  rw [hclog] at hceil
  have hmreal : (2 * M : ℕ) ≤ (2 : ℝ) * familyCoefficient t * (n : ℝ) ^ (2 * t) := by
    have hh : 2 * M ≤ 2 * familyCoefficient t * n ^ (2 * t) := by
      nlinarith [Nat.mul_le_mul_left 2 hsize]
    exact_mod_cast hh
  have hlogle := (Real.logb_le_logb htwo (by positivity) (by positivity)).mpr hmreal
  have he : Real.logb (2 : ℝ) ((2 : ℝ) * familyCoefficient t * (n : ℝ) ^ (2 * t)) =
      1 + logTwo (familyCoefficient t) + (2 * t : ℕ) * logTwo n := by
    rw [Real.logb_mul (by positivity) (by positivity),
      Real.logb_mul (by norm_num) hcpos.ne', Real.logb_self_eq_one htwo, Real.logb_pow]
    rfl
  rw [he] at hlogle
  unfold checkRows redundancyConstant
  push_cast at hceil hlogle ⊢
  linarith

 theorem checkRows_eventual_threshold (t : ℕ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ M : ℕ,
      1 ≤ M → M ≤ familyCoefficient t * n ^ (2 * t) →
      checkRows M < n ∧
      (checkRows M + 1 : ℕ) ≤ (2 * t : ℕ) * logTwo n + redundancyConstant t := by
  have hsmall : (fun x : ℝ => (2 * t : ℕ) * Real.logb 2 x + redundancyConstant t) =o[atTop] id :=
    (Real.isLittleO_logb_id_atTop.const_mul_left (2 * t : ℕ)).add
      (Asymptotics.isLittleO_const_id_atTop (redundancyConstant t))
  have hbound := hsmall.bound (by norm_num : (0 : ℝ) < 1 / 2)
  have hbN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hbound
  have hevent : ∀ᶠ n : ℕ in atTop,
      (2 * t : ℕ) * logTwo n + redundancyConstant t < n := by
    filter_upwards [hbN, eventually_ge_atTop 1] with n hb hn
    change |(2 * t : ℕ) * logTwo n + redundancyConstant t| ≤ (1 / 2 : ℝ) * |(n : ℝ)| at hb
    simp only [abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] at hb
    have ha := le_abs_self ((2 * t : ℕ) * logTwo n + redundancyConstant t)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro n hn M hM hsize
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hb := checkRows_redundancy_bound t n M hn1 hM hsize
  refine ⟨?_, hb⟩
  have hh := lt_of_le_of_lt hb (hN n (le_trans (le_max_left _ _) hn))
  have : checkRows M + 1 < n := by exact_mod_cast hh
  omega

end EditGV897.Main


open EditGV897.Main

theorem solution (t : ℕ) (ht : 1 ≤ t) :
    0 < redundancyConstant t ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        EditFamily t F ∧ F.length ≤ familyCoefficient t * n ^ (2 * t) ∧
        P.rows.length = checkRows F.length ∧ P.rows.length < n ∧ FullRowRank P.rows ∧
        P.beta.length = P.rows.length ∧
        witnessSum F P.rows Finset.univ ≤ F.length * 2 ^ (n - P.rows.length) ∧
        witnessSum F P.rows Finset.univ ≤ 2 ^ (n - 1) ∧
        (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) ∧
        (P.rows.length + 1 : ℕ) ≤ (2 * t : ℕ) * logTwo n + redundancyConstant t := by
  obtain ⟨N, hN, hnum⟩ := checkRows_eventual_threshold t
  obtain ⟨_, _, _, _, hsyn⟩ := choosing_syndrome
  refine ⟨redundancyConstant_pos t, N, hN, ?_⟩
  intro n hn
  have hF := canonicalFamily_editFamily t n
  have hsize := canonicalFamily_length_le t n (le_trans hN hn)
  obtain ⟨hb, hred⟩ := hnum n hn _ hF.1 hsize
  obtain ⟨hrows, hrank, hw1, hw2⟩ := matrix_certificates n t (canonicalFamily t n) ht hF hb
  have hlt : (chooseMatrix (canonicalFamily t n)).length < n := by simpa only [hrows] using hb
  obtain ⟨hbeta, _, _, _, hroot, _⟩ :=
    hsyn n t (canonicalFamily t n) (chooseMatrix (canonicalFamily t n)) ht hF hrows hlt hrank hw2
  dsimp only [setup, messageLength]
  refine ⟨hF, hsize, hrows, hlt, hrank, hbeta, hw1, hw2, hroot, ?_⟩
  simpa only [hrows] using hred