-- Prove2me | solution 1 for EditGV897.Main.choosing_syndrome
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:38:12.652416+00:00
-- url     : https://prove2.me/submissions/37d4cc88-26d1-4c23-af45-c3959a259bac

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_witness_count_correct

import Theorems.Thm_EditGV897_Main_syndrome_program

namespace EditGV897.Main
private theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witness_count_correct n F G E
end EditGV897.Main


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

 theorem affineSet_card_of_independent {n : ℕ} (E : List (Equation n))
    (hLI : FullRowRank (E.map Prod.fst)) : (affineSet E).card = 2 ^ (n - E.length) := by
  classical
  let A : Matrix (Fin E.length) (Fin n) Bit := fun i => (E.get i).1
  let y : Fin E.length → Bit := fun i => (E.get i).2
  let f : Word n →ₗ[Bit] (Fin E.length → Bit) := A.mulVecLin
  have hLI' : LinearIndependent Bit A.row := by
    let emb : Fin E.length → Fin (E.map Prod.fst).length := fun i => ⟨i.val, by simpa using i.isLt⟩
    have hemb : Function.Injective emb := by
      intro i j h
      have hv := congrArg (fun z : Fin (E.map Prod.fst).length => z.val) h
      exact Fin.ext hv
    have hh := hLI.comp emb hemb
    convert hh using 1
    funext i
    simp [A, Matrix.row, emb, List.get_eq_getElem]
  have hrank : A.rank = E.length := by simpa using hLI'.rank_matrix
  have hdim : Module.finrank Bit (LinearMap.range f) = E.length := by
    exact hrank
  have hsurj : Function.Surjective f := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    simpa using hdim
  obtain ⟨x0, hx0⟩ := hsurj y
  have hker : Module.finrank Bit (LinearMap.ker f) = n - E.length := by
    have hh := f.finrank_range_add_finrank_ker
    rw [hdim] at hh
    have hdn : Module.finrank Bit (Word n) = n := by
      simp [Word, DeletionHash.MixedEdit.Word]
    rw [hdn] at hh
    omega
  let eqv : {x : Word n // f x = y} ≃ LinearMap.ker f :=
    { toFun := fun x => ⟨x.1 - x0, by simp [map_sub, x.2, hx0]⟩
      invFun := fun z => ⟨z.1 + x0, by simp [map_add, z.2, hx0]⟩
      left_inv := by intro x; ext i; simp
      right_inv := by intro z; ext i; simp }
  have hspec (x : Word n) : (∀ e ∈ E, equationHolds e x) ↔ f x = y := by
    constructor
    · intro h
      funext i
      exact h _ (List.get_mem E i)
    · intro h e he
      obtain ⟨i, hi⟩ := List.get_of_mem he
      have hh := congrFun h i
      change dot (E.get i).1 x = (E.get i).2 at hh
      simpa only [hi, equationHolds] using hh
  have hcard : (affineSet E).card = Fintype.card {x : Word n // f x = y} := by
    simp only [Fintype.card_subtype]
    congr 1
    ext x
    simp only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and, hspec]
  rw [hcard, Fintype.card_congr eqv, Module.card_eq_pow_finrank (K := Bit), hker]
  simp [Bit, ZMod.card]

end EditGV897.Main


namespace EditGV897.Main

 theorem mem_allBitLists_iff (b : ℕ) (p : List Bit) : p ∈ allBitLists b ↔ p.length = b := by
  induction b generalizing p with
  | zero => simp [allBitLists]
  | succ b ih =>
    constructor
    · intro hp
      simp only [allBitLists, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      obtain ⟨q, hq, hp⟩ := hp
      have hlen := (ih q).mp hq
      rcases hp with rfl | rfl <;> simp [hlen]
    · intro hp
      cases p using List.reverseRecOn with
      | nil => simp at hp
      | append_singleton p a =>
        have hlen : p.length = b := by simp only [List.length_append, List.length_singleton] at hp; omega
        have hm := (ih p).mpr hlen
        simp only [allBitLists, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
        refine ⟨p, hm, ?_⟩
        rcases bit_zero_or_one a with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

private theorem fold_min_le_start (value : List Bit → ℕ) (L : List (List Bit)) (best : List Bit) :
    value (L.foldl (fun best a => if value a < value best then a else best) best) ≤ value best := by
  induction L generalizing best with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldl_cons]
    have hh := ih (if value a < value best then a else best)
    split_ifs at hh ⊢ with h <;> omega

private theorem fold_min_le_mem (value : List Bit → ℕ) (L : List (List Bit)) (best a : List Bit)
    (ha : a ∈ L) :
    value (L.foldl (fun best a => if value a < value best then a else best) best) ≤ value a := by
  induction L generalizing best with
  | nil => simp at ha
  | cons c L ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ha with hca | ha
    · subst a
      have hh := fold_min_le_start value L (if value c < value best then c else best)
      split_ifs at hh ⊢ with h <;> omega
    · exact ih _ ha

private theorem fold_min_length (value : List Bit → ℕ) (L : List (List Bit)) (best : List Bit) (b : ℕ)
    (hbest : best.length = b) (hL : ∀ a ∈ L, a.length = b) :
    (L.foldl (fun best a => if value a < value best then a else best) best).length = b := by
  induction L generalizing best with
  | nil => exact hbest
  | cons c L ih =>
    simp only [List.foldl_cons]
    apply ih
    · split_ifs
      · exact hL c (by simp)
      · exact hbest
    · intro a ha; exact hL a (by simp [ha])

 theorem affineSet_coset {n : ℕ} (G : Rows n) (β : List Bit) (hβ : β.length = G.length) :
    affineSet (cosetEquations G β) = coset G β := by
  classical
  ext x
  simp only [affineSet, coset, Finset.mem_filter, Finset.mem_univ, true_and, cosetEquations_spec G β hβ x]

 theorem coset_card {n : ℕ} (G : Rows n) (β : List Bit) (hG : FullRowRank G)
    (hβ : β.length = G.length) : (coset G β).card = 2 ^ (n - G.length) := by
  have hm : (G.zip β).map Prod.fst = G := by
    rw [List.map_fst_zip]
    simp [hβ]
  have hl : (G.zip β).length = G.length := by simp [hβ]
  rw [← affineSet_coset G β hβ]
  have hc := affineSet_card_of_independent (G.zip β) (by rw [hm]; exact hG)
  simpa only [cosetEquations, hl] using hc

 theorem chooseSyndrome_min {n : ℕ} (F : Family n) (G : Rows n) :
    (chooseSyndrome F G).length = G.length ∧
    ∀ γ : List Bit, γ.length = G.length →
      witnessSum F G (coset G (chooseSyndrome F G)) ≤ witnessSum F G (coset G γ) := by
  classical
  let val := fun β => witnessCount F G (cosetEquations G β)
  have hlen : (chooseSyndrome F G).length = G.length :=
    fold_min_length val (allBitLists G.length) (List.replicate G.length 0) G.length
      (by simp) (fun a ha => (mem_allBitLists_iff _ _).mp ha)
  refine ⟨hlen, ?_⟩
  intro γ hγ
  have hh := fold_min_le_mem val (allBitLists G.length) (List.replicate G.length 0) γ
    ((mem_allBitLists_iff _ _).mpr hγ)
  change witnessCount F G (cosetEquations G (chooseSyndrome F G)) ≤ witnessCount F G (cosetEquations G γ) at hh
  simpa only [witnessCount_correct, affineSet_coset G _ hlen, affineSet_coset G _ hγ] using hh

 theorem witnessSum_coset_partition {n : ℕ} (F : Family n) (G : Rows n) :
    ∑ γ : Word G.length, witnessSum F G (coset G (wordList γ)) = witnessSum F G Finset.univ := by
  classical
  simp only [witnessSum, coset, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hs : (syndrome G x).length = G.length := by simp [syndrome]
  have he (γ : Word G.length) : syndrome G x = wordList γ ↔ γ = listWord G.length (syndrome G x) := by
    constructor
    · intro h
      have hh := congrArg (listWord G.length) h
      simpa only [listWord_wordList] using hh.symm
    · intro h
      rw [h, wordList_listWord _ hs]
  simp_rw [he]
  simp

 theorem chooseSyndrome_certificates {n : ℕ} (F : Family n) (G : Rows n)
    (hsmall : G.length < n) (hG : FullRowRank G)
    (hW : witnessSum F G Finset.univ ≤ 2 ^ (n - 1)) :
    let β := chooseSyndrome F G
    β.length = G.length ∧
    (∀ γ : List Bit, γ.length = G.length → witnessSum F G (coset G β) ≤ witnessSum F G (coset G γ)) ∧
    witnessSum F G (coset G β) ≤ 2 ^ (n - G.length - 1) ∧
    (coset G β).card = 2 ^ (n - G.length) ∧
    (2 ^ (n - G.length - 1) : ℤ) ≤ signedBound F G (coset G β) := by
  classical
  obtain ⟨hlen, hmin⟩ := chooseSyndrome_min F G
  have hsum : 2 ^ G.length * witnessSum F G (coset G (chooseSyndrome F G)) ≤
      witnessSum F G Finset.univ := by
    rw [← witnessSum_coset_partition F G]
    calc
      _ = ∑ _γ : Word G.length, witnessSum F G (coset G (chooseSyndrome F G)) := by
        simp [Word, DeletionHash.MixedEdit.Word, Bit, ZMod.card, Nat.mul_comm]
      _ ≤ _ := by apply Finset.sum_le_sum; intro γ hγ; exact hmin _ (by simp)
  have hpow : 2 ^ (n - 1) = 2 ^ G.length * 2 ^ (n - G.length - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hhalf : witnessSum F G (coset G (chooseSyndrome F G)) ≤ 2 ^ (n - G.length - 1) := by
    have hh := hsum.trans hW
    rw [hpow] at hh
    have hp : 0 < 2 ^ G.length := by positivity
    nlinarith
  have hcard := coset_card G (chooseSyndrome F G) hG hlen
  refine ⟨hlen, hmin, hhalf, hcard, ?_⟩
  unfold signedBound
  rw [hcard]
  have hpow2Nat : (2 ^ (n - G.length) : ℕ) = 2 * 2 ^ (n - G.length - 1) := by
    have he : n - G.length = (n - G.length - 1) + 1 := by omega
    conv_lhs => rw [he, pow_succ]
    omega
  have hpow2 : ((2 ^ (n - G.length) : ℕ) : ℤ) = 2 * 2 ^ (n - G.length - 1) := by
    exact_mod_cast hpow2Nat
  rw [hpow2]
  have hwz : (witnessSum F G (coset G (chooseSyndrome F G)) : ℤ) ≤ 2 ^ (n - G.length - 1) := by
    exact_mod_cast hhalf
  omega

end EditGV897.Main


open EditGV897.Main

theorem solution :
    ∃ (selector : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (G : Rows n),
        1 ≤ t → EditFamily t F → G.length = checkRows F.length → G.length < n →
        FullRowRank G → witnessSum F G Finset.univ ≤ 2 ^ (n - 1) →
        let β := chooseSyndrome F G
        β.length = G.length ∧
        (∀ γ : List Bit, γ.length = G.length →
          witnessSum F G (coset G β) ≤ witnessSum F G (coset G γ)) ∧
        witnessSum F G (coset G β) ≤ 2 ^ (n - G.length - 1) ∧
        (coset G β).card = 2 ^ (n - G.length) ∧
        (2 ^ (n - G.length - 1) : ℤ) ≤ signedBound F G (coset G β) ∧
        Runs selector (syndromeInput F G) (bitCode β) (polyBudget A d (n + F.length)) := by
  obtain ⟨selector, A, d, hA, hr⟩ := syndrome_program
  refine ⟨selector, A, d, hA, ?_⟩
  intro n t F G ht hF hrows hsmall hG hW
  obtain ⟨hlen, hmin, hhalf, hcard, hroot⟩ := chooseSyndrome_certificates F G hsmall hG hW
  exact ⟨hlen, hmin, hhalf, hcard, hroot, hr n t F G ht hF hrows hsmall hG hW⟩