-- Prove2me | solution 1 for EditGV897.Main.affine_count_correct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:21:44.773712+00:00
-- url     : https://prove2.me/submissions/53aae467-196e-4be2-b5f0-7a716ae03777

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

 theorem dot_add_left {n : ℕ} (x y h : Word n) : dot (x + y) h = dot x h + dot y h := by
  simp [dot, add_mul, Finset.sum_add_distrib]

 theorem xorEquation_holds_iff {n : ℕ} (e p : Equation n) (x : Word n)
    (hp : equationHolds p x) : equationHolds (xorEquation e p) x ↔ equationHolds e x := by
  unfold equationHolds xorEquation at *
  simp only [dot_add_left, hp, add_left_inj]

 private theorem holds_erase {n : ℕ} (E : List (Equation n)) (p : Equation n)
    (hp : p ∈ E) (x : Word n) :
    (∀ e ∈ E, equationHolds e x) ↔
      equationHolds p x ∧ ∀ e ∈ E.erase p, equationHolds e x := by
  constructor
  · intro h
    exact ⟨h p hp, fun e he => h e (List.mem_of_mem_erase he)⟩
  · rintro ⟨hpx, h⟩ e he
    by_cases hep : e = p
    · simpa only [hep] using hpx
    · exact h e ((List.mem_erase_of_ne hep).mpr he)

 theorem gaussian_affineSet {n : ℕ} (fuel k : ℕ) (E : List (Equation n)) :
    affineSet (gaussian fuel k E) = affineSet E := by
  classical
  induction fuel generalizing k E with
  | zero => rfl
  | succ fuel ih =>
    unfold gaussian
    split_ifs with hk
    · cases hf : E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
      | none => exact ih (k + 1) E
      | some p =>
        have hp : p ∈ E := List.mem_of_find?_eq_some hf
        ext x
        simp only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and,
          List.forall_mem_cons]
        have hir : (∀ e ∈ gaussian fuel (k + 1)
              ((E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p)),
              equationHolds e x) ↔
            ∀ e ∈ (E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p),
              equationHolds e x := by
          have hh := congrArg (fun S : Finset (Word n) => x ∈ S) (ih (k + 1)
            ((E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p)))
          simpa only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and] using Iff.of_eq hh
        rw [hir, holds_erase E p hp x]
        apply and_congr_right
        intro hpx
        simp only [List.forall_mem_map]
        apply forall_congr'
        intro e
        apply forall_congr'
        intro he
        split_ifs
        · rfl
        · exact xorEquation_holds_iff e p x hpx
    · rfl

 theorem gaussian_preserves_zero {n : ℕ} (fuel k : ℕ) (E : List (Equation n)) (j : Fin n)
    (hz : ∀ e ∈ E, e.1 j = 0) : ∀ e ∈ gaussian fuel k E, e.1 j = 0 := by
  classical
  induction fuel generalizing k E with
  | zero => exact hz
  | succ fuel ih =>
    unfold gaussian
    split_ifs with hk
    · cases hf : E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
      | none => exact ih (k + 1) E hz
      | some p =>
        have hp := hz p (List.mem_of_find?_eq_some hf)
        simp only [List.forall_mem_cons]
        refine ⟨hp, ih (k + 1) _ ?_⟩
        intro e he
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
        split_ifs
        · exact hz a (List.mem_of_mem_erase ha)
        · simp only [xorEquation, Pi.add_apply, hz a (List.mem_of_mem_erase ha), hp, add_zero]
    · exact hz

private def nonzeroRows {n : ℕ} (E : List (Equation n)) : Rows n := by
  classical
  exact (E.filter (fun e => decide (e.1 ≠ 0))).map Prod.fst

private theorem zero_column_span {n : ℕ} (G : Rows n) (j : Fin n)
    (hz : ∀ g ∈ G, g j = 0) (v : Word n)
    (hv : v ∈ Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) : v j = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨i, rfl⟩ := hv; exact hz _ (List.get_mem G i)
  | zero => rfl
  | add x y hx hy hx0 hy0 => simp only [Pi.add_apply, hx0, hy0, add_zero]
  | smul a x hx hx0 => simp only [Pi.smul_apply, hx0, smul_zero]

private theorem nonzeroRows_rank_empty {n : ℕ} (E : List (Equation n))
    (hz : ∀ e ∈ E, e.1 = 0) : FullRowRank (nonzeroRows E) := by
  classical
  have hf : E.filter (fun e => decide (e.1 ≠ 0)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [hz e he]
  unfold nonzeroRows
  rw [hf]
  change FullRowRank ([] : Rows n)
  unfold FullRowRank
  letI : IsEmpty (Fin ([] : Rows n).length) := by
    change IsEmpty (Fin 0)
    infer_instance
  exact linearIndependent_empty_type

private theorem fullRowRank_cons {n : ℕ} (v : Word n) (G : Rows n)
    (hG : FullRowRank G)
    (hv : v ∉ Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) :
    FullRowRank (v :: G) := by
  have hh := hG.finCons hv
  have heq : (fun i : Fin (G.length + 1) => (v :: G).get i) =
      Fin.cons v (fun i : Fin G.length => G.get i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  unfold FullRowRank
  change LinearIndependent Bit (fun i : Fin (G.length + 1) => (v :: G).get i)
  rw [heq]
  exact hh

private theorem eliminate_zero_prefix {n k : ℕ} (hk : k < n)
    (E : List (Equation n)) (p : Equation n) (hp : p ∈ E)
    (hpk : p.1 ⟨k, hk⟩ ≠ 0)
    (hz : ∀ j : Fin n, j.val < k → ∀ e ∈ E, e.1 j = 0) :
    ∀ j : Fin n, j.val < k + 1 →
      ∀ e ∈ (E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p), e.1 j = 0 := by
  classical
  intro j hj e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have haE := List.mem_of_mem_erase ha
  by_cases hjk : j.val < k
  · split_ifs
    · exact hz j hjk a haE
    · simp only [xorEquation, Pi.add_apply, hz j hjk a haE, hz j hjk p hp, add_zero]
  · have hjeq : j = ⟨k, hk⟩ := by apply Fin.ext; change j.val = k; omega
    subst j
    split_ifs with hak
    · exact hak
    · have hpa : p.1 ⟨k, hk⟩ = 1 := (bit_zero_or_one _).resolve_left hpk
      have haa : a.1 ⟨k, hk⟩ = 1 := (bit_zero_or_one _).resolve_left hak
      simp only [xorEquation, Pi.add_apply, hpa, haa, CharTwo.add_self_eq_zero]

theorem gaussian_nonzero_independent {n : ℕ} (fuel k : ℕ) (E : List (Equation n))
    (hlen : n ≤ k + fuel)
    (hz : ∀ j : Fin n, j.val < k → ∀ e ∈ E, e.1 j = 0) :
    FullRowRank (nonzeroRows (gaussian fuel k E)) := by
  classical
  induction fuel generalizing k E with
  | zero =>
    apply nonzeroRows_rank_empty
    intro e he
    funext j
    exact hz j (by omega) e he
  | succ fuel ih =>
    unfold gaussian
    split_ifs with hk
    · cases hf : E.find? (fun e => decide (e.1 ⟨k, hk⟩ ≠ 0)) with
      | none =>
        apply ih (k + 1) E (by omega)
        intro j hj e he
        by_cases hjk : j.val < k
        · exact hz j hjk e he
        · have hjk' : j = ⟨k, hk⟩ := by apply Fin.ext; change j.val = k; omega
          subst j
          have hh := List.find?_eq_none.mp hf e he
          simpa only [decide_eq_true_eq, not_not] using hh
      | some p =>
        have hp := List.mem_of_find?_eq_some hf
        have hpk : p.1 ⟨k, hk⟩ ≠ 0 := by simpa using List.find?_some hf
        have hpv : p.1 ≠ 0 := by intro h; apply hpk; rw [h]; rfl
        have hzero := eliminate_zero_prefix hk E p hp hpk hz
        let R := gaussian fuel (k + 1)
          ((E.erase p).map (fun e => if e.1 ⟨k, hk⟩ = 0 then e else xorEquation e p))
        have hrec : FullRowRank (nonzeroRows R) := ih (k + 1) _ (by omega) hzero
        have hpv' : decide (p.1 ≠ 0) = true := decide_eq_true hpv
        have heq : nonzeroRows (p :: R) = p.1 :: nonzeroRows R := by
          unfold nonzeroRows
          rw [List.filter_cons, hpv']
          rfl
        change FullRowRank (nonzeroRows (p :: R))
        rw [heq]
        apply fullRowRank_cons p.1 _ hrec
        intro hspan
        apply hpk
        apply zero_column_span _ ⟨k, hk⟩ _ _ hspan
        intro g hg
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
        obtain ⟨he, _⟩ := List.mem_filter.mp he
        exact gaussian_preserves_zero fuel (k + 1) _ ⟨k, hk⟩ (hzero ⟨k, hk⟩ (by change k < k + 1; omega)) e he
    · apply nonzeroRows_rank_empty
      intro e he
      funext j
      exact hz j (by omega) e he

private theorem affineSet_remove_zero {n : ℕ} (E : List (Equation n))
    (hzero : ∀ e ∈ E, e.1 = 0 → e.2 = 0) :
    affineSet E = affineSet (E.filter (fun e => decide (e.1 ≠ 0))) := by
  classical
  ext x
  simp only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h e he
    exact h e (List.mem_filter.mp he).1
  · intro h e he
    by_cases hz : e.1 = 0
    · simp [equationHolds, hz, hzero e he hz, dot]
    · exact h e (List.mem_filter.mpr ⟨he, by exact decide_eq_true hz⟩)

private theorem affineSet_inconsistent {n : ℕ} (E : List (Equation n))
    (e : Equation n) (he : e ∈ E) (hz : e.1 = 0) (hb : e.2 ≠ 0) : affineSet E = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := (Finset.mem_filter.mp hx).2 e he
  apply hb
  symm
  simpa [equationHolds, hz, dot] using hh

 theorem affineCount_correct {n : ℕ} (E : List (Equation n)) :
    affineCount E = (affineSet E).card := by
  classical
  let R := gaussian n 0 E
  have hLI : FullRowRank (nonzeroRows R) :=
    gaussian_nonzero_independent n 0 E (by omega) (by intro j hj; omega)
  have hset : affineSet R = affineSet E := gaussian_affineSet n 0 E
  rw [← hset]
  change (if R.any (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0)) then 0
    else 2 ^ (n - pivotCount R)) = (affineSet R).card
  split_ifs with hbad
  · obtain ⟨e, he, heq⟩ := List.any_eq_true.mp hbad
    have hb : e.1 = 0 ∧ e.2 ≠ 0 := by simpa only [decide_eq_true_eq] using heq
    rw [affineSet_inconsistent R e he hb.1 hb.2, Finset.card_empty]
  · have hz : ∀ e ∈ R, e.1 = 0 → e.2 = 0 := by
      intro e he he0
      by_contra he2
      apply hbad
      exact List.any_eq_true.mpr ⟨e, he, by simpa only [decide_eq_true_eq] using And.intro he0 he2⟩
    rw [affineSet_remove_zero R hz]
    have hc := affineSet_card_of_independent (R.filter (fun e => decide (e.1 ≠ 0))) hLI
    exact hc.symm

end EditGV897.Main

open EditGV897.Main

theorem solution (n : ℕ) (E : List (Equation n)) : affineCount E = (affineSet E).card := affineCount_correct E