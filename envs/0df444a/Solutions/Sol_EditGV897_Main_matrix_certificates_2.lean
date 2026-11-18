-- Prove2me | solution 2 for EditGV897.Main.matrix_certificates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T02:48:50.619363+00:00
-- url     : https://prove2.me/submissions/4e210b1b-37c6-4ec7-9871-78d6c592f005

import Definitions.Def_EditGV897_Main_Codec

import Theorems.Thm_EditGV897_Main_partial_row_semantics

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

private theorem affineCount_correct {n : ℕ} (E : List (Equation n)) :
    affineCount E = (affineSet E).card := affine_count_correct n E

private theorem witnessCount_correct {n : ℕ} (F : Family n) (G : Rows n) (E : List (Equation n)) :
    witnessCount F G E = witnessSum F G (affineSet E) := witness_count_correct n F G E

theorem gaussian_pivotCount_le {n : ℕ} (E : List (Equation n)) :
    pivotCount (gaussian n 0 E) ≤ n := by
  have hi := gaussian_nonzero_independent n 0 E (by omega) (by intro j hj; omega)
  have hh := hi.fintype_card_le_finrank
  simpa [nonzeroRows, pivotCount, Word, DeletionHash.MixedEdit.Word] using hh

end EditGV897.Main


namespace EditGV897.Main

 theorem homogeneous_affineSet_card {n : ℕ} (G : Rows n) :
    (affineSet (G.map (fun h => (h, (0 : Bit))))).card =
      2 ^ (n - Matrix.rank (fun i : Fin G.length => G.get i)) := by
  classical
  let A : Matrix (Fin G.length) (Fin n) Bit := fun i => G.get i
  let f : Word n →ₗ[Bit] (Fin G.length → Bit) := A.mulVecLin
  have hker : Module.finrank Bit (LinearMap.ker f) = n - A.rank := by
    have hh := f.finrank_range_add_finrank_ker
    have hdn : Module.finrank Bit (Word n) = n := by simp [Word, DeletionHash.MixedEdit.Word]
    change A.rank + _ = _ at hh
    rw [hdn] at hh
    omega
  have hs (x : Word n) : x ∈ affineSet (G.map (fun h => (h, (0 : Bit)))) ↔ x ∈ LinearMap.ker f := by
    simp only [affineSet, Finset.mem_filter, Finset.mem_univ, true_and, List.forall_mem_map]
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      funext i
      exact h _ (List.get_mem G i)
    · intro h g hg
      obtain ⟨i, hi⟩ := List.get_of_mem hg
      have hh := congrFun h i
      change dot (G.get i) x = 0 at hh
      simpa only [hi, equationHolds] using hh
  have hc : (affineSet (G.map (fun h => (h, (0 : Bit))))).card = Fintype.card (LinearMap.ker f) := by
    rw [Fintype.card_subtype]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs]
  rw [hc, Module.card_eq_pow_finrank (K := Bit), hker]
  simp [Bit, ZMod.card, A]

 theorem rowRank_eq_matrix_rank {n : ℕ} (G : Rows n) :
    rowRank G = Matrix.rank (fun i : Fin G.length => G.get i) := by
  classical
  let E := G.map (fun h => (h, (0 : Bit)))
  have hzero : (0 : Word n) ∈ affineSet E := by
    simp [affineSet, E, equationHolds, dot]
  have hcount := affineCount_correct E
  have hcard := homogeneous_affineSet_card G
  have hpos : 0 < affineCount E := by rw [hcount]; exact Finset.card_pos.mpr ⟨0, hzero⟩
  have hnobad : ¬ (gaussian n 0 E).any (fun e => decide (e.1 = 0 ∧ e.2 ≠ 0)) = true := by
    intro hbad
    unfold affineCount at hpos
    rw [if_pos hbad] at hpos
    omega
  have hformula : affineCount E = 2 ^ (n - rowRank G) := by
    unfold affineCount
    rw [if_neg hnobad]
    rfl
  have hpow : 2 ^ (n - rowRank G) = 2 ^ (n - Matrix.rank (fun i : Fin G.length => G.get i)) := by
    rw [← hformula, hcount, hcard]
  have hexp : n - rowRank G = n - Matrix.rank (fun i : Fin G.length => G.get i) := by
    exact Nat.pow_right_injective (by omega : 1 < 2) hpow
  have hle := gaussian_pivotCount_le E
  have hle' : Matrix.rank (fun i : Fin G.length => G.get i) ≤ n := by
    simpa using Matrix.rank_le_card_width (fun i : Fin G.length => G.get i)
  change rowRank G ≤ n at hle
  omega

end EditGV897.Main


namespace EditGV897.Main

 theorem fullRowRank_iff_rowRank {n : ℕ} (G : Rows n) : FullRowRank G ↔ rowRank G = G.length := by
  rw [rowRank_eq_matrix_rank]
  constructor
  · intro h
    simpa only [Fintype.card_fin] using h.rank_matrix
  · intro h
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simp only [Fintype.card_fin, Set.finrank]
    have he := Matrix.rank_eq_finrank_span_row (fun i : Fin G.length => G.get i)
    change Matrix.rank (fun i : Fin G.length => G.get i) =
      Module.finrank Bit (Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) at he
    rw [← he]
    exact h.symm

 theorem fullRowRank_snoc {n : ℕ} (G : Rows n) (v : Word n) (hG : FullRowRank G)
    (hv : v ∉ Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) :
    FullRowRank (G ++ [v]) := by
  have hh := hG.finSnoc hv
  have hlen : (G ++ [v]).length = G.length + 1 := by simp
  have heq : (fun i : Fin (G.length + 1) => (G ++ [v]).get (Fin.cast hlen.symm i)) =
      Fin.snoc (fun i : Fin G.length => G.get i) v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.cast, Fin.snoc, List.get_eq_getElem, List.getElem_append]
    · simp [Fin.cast, Fin.snoc, List.get_eq_getElem, List.getElem_append, j.isLt]
  have hh' : LinearIndependent Bit (fun i : Fin (G.length + 1) => (G ++ [v]).get
      (Fin.cast hlen.symm i)) := by
    rw [heq]
    exact hh
  have hc := hh'.comp (Fin.cast hlen) (Fin.cast_injective hlen)
  simpa only [Function.comp_def, Fin.cast_cast, Fin.cast_refl, id_eq, FullRowRank] using hc

 theorem unitWords_span (n : ℕ) :
    Submodule.span Bit (Set.range (fun i : Fin n => unitWord n i.val)) = ⊤ := by
  apply top_le_iff.mp
  intro x hx
  have hrep : x = ∑ i : Fin n, x i • unitWord n i.val := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitWord,
      mul_ite, mul_one, mul_zero]
    simp only [← Fin.ext_iff]
    simp
  rw [hrep]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

 theorem exists_unitWord_independent {n : ℕ} (G : Rows n) (hG : FullRowRank G) (hlen : G.length < n) :
    ∃ i : Fin n, unitWord n i.val ∉ Submodule.span Bit (Set.range (fun j : Fin G.length => G.get j)) := by
  by_contra hall
  push_neg at hall
  have ht : Submodule.span Bit (Set.range (fun j : Fin G.length => G.get j)) = ⊤ := by
    apply top_le_iff.mp
    rw [← unitWords_span n]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hall i
  let b := Module.Basis.mk hG (show ⊤ ≤ Submodule.span Bit (Set.range (fun j : Fin G.length => G.get j)) by rw [ht])
  have hd := Module.finrank_eq_card_basis b
  have hdim : Module.finrank Bit (Word n) = n := by simp [Word, DeletionHash.MixedEdit.Word]
  rw [hdim, Fintype.card_fin] at hd
  omega

 theorem completionRow_independent {n : ℕ} (G : Rows n) (hG : FullRowRank G) (hlen : G.length < n) :
    FullRowRank (G ++ [completionRow G]) := by
  classical
  obtain ⟨i, hi⟩ := exists_unitWord_independent G hG hlen
  have hr : rowRank (G ++ [unitWord n i.val]) = G.length + 1 := by
    have hh := (fullRowRank_iff_rowRank _).mp (fullRowRank_snoc G _ hG hi)
    simpa only [List.length_append, List.length_singleton] using hh
  unfold completionRow
  cases hf : (List.range n).find? (fun k => rowRank (G ++ [unitWord n k]) == G.length + 1) with
  | none =>
    have hh := List.find?_eq_none.mp hf i.val (by simpa only [List.mem_range] using i.isLt)
    simp only [hr, beq_self_eq_true, not_true_eq_false] at hh
  | some k =>
    apply (fullRowRank_iff_rowRank _).mpr
    have hh := List.find?_some hf
    simpa only [beq_iff_eq, List.length_append, List.length_singleton] using hh

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

 theorem dot_zero_of_mem_span {n : ℕ} (G : Rows n) (d h : Word n)
    (hd : syndrome G d = G.map (fun _ => 0))
    (hh : h ∈ Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) : dot h d = 0 := by
  induction hh using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact List.map_inj_left.mp hd _ (List.get_mem G i)
  | zero => simp [dot]
  | add x y hx hy hxd hyd => rw [dot_add_left, hxd, hyd, add_zero]
  | smul a x hx hxd =>
    have he : dot (a • x) d = a * dot x d := by simp [dot, mul_assoc, Finset.mul_sum]
    rw [he, hxd, mul_zero]

 theorem witnessSum_append_le {n : ℕ} (F : Family n) (G : Rows n) (h : Word n)
    (S : Finset (Word n)) : witnessSum F (G ++ [h]) S ≤ witnessSum F G S := by
  classical
  apply Finset.sum_le_sum
  intro x hx
  unfold witnessesAt
  simp only [← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro f hf hc
  simp only [decide_eq_true_eq] at hc ⊢
  exact ⟨hc.1, (syndrome_append_zero G h _).mp hc.2 |>.1⟩

 theorem witnessSum_append_of_mem_span {n : ℕ} (F : Family n) (G : Rows n) (h : Word n)
    (S : Finset (Word n))
    (hh : h ∈ Submodule.span Bit (Set.range (fun i : Fin G.length => G.get i))) :
    witnessSum F (G ++ [h]) S = witnessSum F G S := by
  classical
  apply Finset.sum_congr rfl
  intro x hx
  unfold witnessesAt
  congr 1
  apply List.filter_congr
  intro f hf
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [syndrome_append_zero]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨h0, h1, dot_zero_of_mem_span G _ h h1 hh⟩

 theorem halving_row_independent {n : ℕ} (F : Family n) (G : Rows n) (h : Word n)
    (hG : FullRowRank G) (hpos : 0 < witnessSum F G Finset.univ)
    (hhalf : 2 * witnessSum F (G ++ [h]) Finset.univ ≤ witnessSum F G Finset.univ) :
    FullRowRank (G ++ [h]) := by
  apply fullRowRank_snoc G h hG
  intro hspan
  rw [witnessSum_append_of_mem_span F G h Finset.univ hspan] at hhalf
  omega

 theorem buildRows_length {n : ℕ} (F : Family n) (k : ℕ) (G : Rows n) :
    (buildRows F k G).length = G.length + k := by
  induction k generalizing G with
  | zero => simp [buildRows]
  | succ k ih =>
    simp only [buildRows]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

 theorem buildRows_certificates {n : ℕ} (F : Family n)
    (hhalf : ∀ G : Rows n, G.length ≤ n →
      2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ)
    (k : ℕ) (G : Rows n) (hlen : G.length + k ≤ n) (hG : FullRowRank G) :
    FullRowRank (buildRows F k G) ∧
      2 ^ k * witnessSum F (buildRows F k G) Finset.univ ≤ witnessSum F G Finset.univ := by
  classical
  induction k generalizing G with
  | zero => exact ⟨hG, by simp [buildRows]⟩
  | succ k ih =>
    have hcount : witnessCount F G [] = witnessSum F G Finset.univ := by
      rw [witnessCount_correct]
      congr 1
      ext x
      simp [affineSet]
    by_cases hz : witnessCount F G [] = 0
    · simp only [buildRows, if_pos hz]
      have hGc := completionRow_independent G hG (by omega)
      have hle := witnessSum_append_le F G (completionRow G) Finset.univ
      have hz' : witnessSum F G Finset.univ = 0 := by omega
      obtain ⟨hr, hw⟩ := ih (G ++ [completionRow G]) (by simp only [List.length_append, List.length_singleton]; omega) hGc
      refine ⟨hr, ?_⟩
      rw [hz']
      have : witnessSum F (G ++ [completionRow G]) Finset.univ = 0 := by omega
      rw [this] at hw
      rw [pow_succ]
      nlinarith
    · simp only [buildRows, if_neg hz]
      have hh := hhalf G (by omega)
      have hGr := halving_row_independent F G _ hG (by omega) hh
      obtain ⟨hr, hw⟩ := ih (G ++ [chooseRow F G]) (by simp only [List.length_append, List.length_singleton]; omega) hGr
      refine ⟨hr, ?_⟩
      rw [pow_succ]
      nlinarith

end EditGV897.Main


namespace EditGV897.Main

 theorem witnessSum_le_card_mul {n : ℕ} (F : Family n) (G : Rows n) (S : Finset (Word n)) :
    witnessSum F G S ≤ S.card * F.length := by
  classical
  calc
    witnessSum F G S ≤ ∑ _x ∈ S, F.length := by
      apply Finset.sum_le_sum
      intro x hx
      exact List.length_filter_le _ _
    _ = S.card * F.length := by simp [Nat.mul_comm]

 theorem chooseMatrix_certificates {n t : ℕ} (F : Family n)
    (ht : 1 ≤ t) (hF : EditFamily t F) (hb : checkRows F.length < n)
    (hhalf : ∀ G : Rows n, G.length ≤ n →
      2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ) :
    let G := chooseMatrix F
    G.length = checkRows F.length ∧ FullRowRank G ∧
    witnessSum F G Finset.univ ≤ F.length * 2 ^ (n - G.length) ∧
    witnessSum F G Finset.univ ≤ 2 ^ (n - 1) := by
  classical
  let b := checkRows F.length
  let G := chooseMatrix F
  have hlen : G.length = b := by simpa [G, b, chooseMatrix] using buildRows_length F (checkRows F.length) []
  have hnil : FullRowRank ([] : Rows n) := by
    unfold FullRowRank
    letI : IsEmpty (Fin ([] : Rows n).length) := by change IsEmpty (Fin 0); infer_instance
    exact linearIndependent_empty_type
  obtain ⟨hrank, hpow⟩ := buildRows_certificates F hhalf b [] (by simpa [b] using Nat.le_of_lt hb) hnil
  have hrank' : FullRowRank G := hrank
  have hinit : witnessSum F [] Finset.univ ≤ F.length * 2 ^ n := by
    have hh := witnessSum_le_card_mul F [] Finset.univ
    simpa [Word, DeletionHash.MixedEdit.Word, Bit, ZMod.card, Nat.mul_comm] using hh
  have hpow' : 2 ^ b * witnessSum F G Finset.univ ≤ F.length * 2 ^ n := hpow.trans hinit
  have hnb : n = b + (n - b) := by dsimp [b]; omega
  have hnexp : 2 ^ n = 2 ^ b * 2 ^ (n - b) := by rw [hnb, pow_add]; congr 2; omega
  have hbound : witnessSum F G Finset.univ ≤ F.length * 2 ^ (n - b) := by
    rw [hnexp] at hpow'
    have hp : 0 < 2 ^ b := by positivity
    nlinarith
  have hbpow : 2 * F.length ≤ 2 ^ b := Nat.le_pow_clog (by omega) _
  have hdouble : 2 * (F.length * 2 ^ (n - b)) ≤ 2 ^ n := by
    rw [hnexp]
    nlinarith [Nat.mul_le_mul_right (2 ^ (n - b)) hbpow]
  have hntwo : 2 ^ n = 2 * 2 ^ (n - 1) := by
    have hn : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn, pow_succ]
    omega
  change G.length = b ∧ FullRowRank G ∧
    witnessSum F G Finset.univ ≤ F.length * 2 ^ (n - G.length) ∧
    witnessSum F G Finset.univ ≤ 2 ^ (n - 1)
  refine ⟨hlen, hrank', ?_, ?_⟩
  · simpa only [hlen] using hbound
  · rw [hntwo] at hdouble
    omega

end EditGV897.Main

open EditGV897.Main

theorem solution (n t : ℕ) (F : Family n)
    (ht : 1 ≤ t) (hF : EditFamily t F) (hb : checkRows F.length < n) :
    let G := chooseMatrix F
    G.length = checkRows F.length ∧ FullRowRank G ∧
    witnessSum F G Finset.univ ≤ F.length * 2 ^ (n - G.length) ∧
    witnessSum F G Finset.univ ≤ 2 ^ (n - 1) := by
  apply chooseMatrix_certificates F ht hF hb
  intro G hG
  exact (partial_row_semantics.2 n t F G ht hF hG).2.2