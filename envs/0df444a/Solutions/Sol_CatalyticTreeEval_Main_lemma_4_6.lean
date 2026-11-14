-- Prove2me | solution 1 for CatalyticTreeEval.Main.lemma_4_6
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-14T01:55:53.196455+00:00
-- url     : https://prove2.me/submissions/c65e7f4c-f1d6-48d8-94d6-6fcb93411839

import Definitions.Def_CatalyticTreeEval_Main_Framework


set_option autoImplicit false

namespace CatalyticTreeEval.Main

@[simp] theorem addAt_same {m d : ℕ} (R : Registers m d) (i : Fin 3) (v : Vec m d) :
    addAt R i v i = R i + v := by simp [addAt]

@[simp] theorem addAt_other {m d : ℕ} (R : Registers m d) (i j : Fin 3)
    (v : Vec m d) (h : j ≠ i) : addAt R i v j = R j := by simp [addAt, h]

theorem addAt_addAt {m d : ℕ} (R : Registers m d) (i : Fin 3) (v w : Vec m d) :
    addAt (addAt R i v) i w = addAt R i (v + w) := by
  funext j
  by_cases h : j = i
  · subst j; simp [add_assoc]
  · simp [h]

@[simp] theorem addAt_zero {m d : ℕ} (R : Registers m d) (i : Fin 3) :
    addAt R i 0 = R := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem addAt_comm {m d : ℕ} (R : Registers m d) (i j : Fin 3) (v w : Vec m d)
    (h : i ≠ j) : addAt (addAt R i v) j w = addAt (addAt R j w) i v := by
  funext a
  by_cases hi : a = i
  · subst a; simp [h]
  · by_cases hj : a = j
    · subst a; simp [h.symm]
    · simp [hi, hj]

@[simp] theorem swapAt_left {m d : ℕ} (R : Registers m d) (i j : Fin 3) (h : i ≠ j) :
    swapAt R i j i = R j := by simp [swapAt, h]

@[simp] theorem swapAt_right {m d : ℕ} (R : Registers m d) (i j : Fin 3) :
    swapAt R i j j = R i := by simp [swapAt]

@[simp] theorem swapAt_other {m d : ℕ} (R : Registers m d) (i j a : Fin 3)
    (hi : a ≠ i) (hj : a ≠ j) : swapAt R i j a = R a := by simp [swapAt, hi, hj]

@[simp] theorem swapAt_swapAt {m d : ℕ} (R : Registers m d) (i j : Fin 3) :
    swapAt (swapAt R i j) i j = R := by
  funext a
  by_cases h : i = j
  · subst j; simp [swapAt]
  · by_cases hi : a = i
    · subst a; simp [h]
    · by_cases hj : a = j
      · subst a; simp [h]
      · simp [hi, hj]

@[simp] theorem oracle_inverse {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (a : ZMod m) (c : Bool) (σ : Fin 2) (R : Registers m d) :
    oracle U V x (-a) c σ (oracle U V x a c σ R) = R := by
  cases c <;> simp [oracle, addAt_addAt]

@[simp] theorem RegisterOp.apply_inverse {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (op : RegisterOp m d) (R : Registers m d) :
    op.inverse.apply U V x (op.apply U V x R) = R := by
  cases op with
  | swap i j => simp [RegisterOp.inverse, RegisterOp.apply]
  | query a c σ => simp [RegisterOp.inverse, RegisterOp.apply]
  | target v => simp [RegisterOp.inverse, RegisterOp.apply, addAt_addAt]

@[simp] theorem execute_nil {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) : execute U V x R [] = R := rfl

@[simp] theorem execute_cons {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) (op : RegisterOp m d)
    (ops : List (RegisterOp m d)) :
    execute U V x R (op :: ops) = execute U V x (op.apply U V x R) ops := rfl

theorem execute_append {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) (as bs : List (RegisterOp m d)) :
    execute U V x R (as ++ bs) = execute U V x (execute U V x R as) bs := by
  simp only [execute, List.foldl_append]

theorem innerProgram_value {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    (innerProgram U V x R).1 = (R 0 ⬝ᵥ V (x 0)) + (R 1 ⬝ᵥ V (x 1)) := by
  simp [innerProgram, oracle, addAt_addAt, dotProduct_add,
    dotProduct_comm]

theorem innerProgram_restores {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    execute U V x R (innerProgram U V x R).2 = R := by
  simp [innerProgram, RegisterOp.apply]

theorem innerProgram_queries {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    ((innerProgram U V x R).2.filter fun op =>
      match op with | .query _ _ _ => true | _ => false).length = 4 := by
  simp [innerProgram]

private def innerPairPerm : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 4

private theorem innerPairPerm_involutive : Function.Involutive innerPairPerm := by
  unfold Function.Involutive
  decide

private theorem innerPairPerm_noFixed : ∀ i, innerPairPerm i ≠ i := by decide

theorem innerProgram_inversePairs {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    InversePairs (innerProgram U V x R).2 := by
  unfold InversePairs
  dsimp [innerProgram, childOps]
  refine ⟨innerPairPerm, innerPairPerm_involutive, innerPairPerm_noFixed, ?_⟩
  intro i
  fin_cases i
  · rfl
  · rfl
  · change RegisterOp.query (1 : ZMod m) true 0 = RegisterOp.query (-(-1)) true 0
    simp
  · rfl
  · change RegisterOp.query (1 : ZMod m) true 1 = RegisterOp.query (-(-1)) true 1
    simp
  · rfl

/-- The complete algebraic content of the literal four-query masked-scalar
program; finite-machine realization is a separate theorem. -/
theorem innerProgram_algebra {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) :
    (innerProgram U V x R).1 = (R 0 ⬝ᵥ V (x 0)) + (R 1 ⬝ᵥ V (x 1)) ∧
    execute U V x R (innerProgram U V x R).2 = R ∧
    InversePairs (innerProgram U V x R).2 ∧
    ((innerProgram U V x R).2.filter fun op =>
      match op with | .query _ _ _ => true | _ => false).length = 4 :=
  ⟨innerProgram_value U V x R, innerProgram_restores U V x R,
    innerProgram_inversePairs U V x R, innerProgram_queries U V x R⟩

end CatalyticTreeEval.Main


set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem oracle_addAt_target {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (a : ZMod m) (c : Bool) (σ : Fin 2)
    (R : Registers m d) (v : Vec m d) :
    oracle U V x a c σ (addAt R 2 v) = addAt (oracle U V x a c σ R) 2 v := by
  unfold oracle
  fin_cases σ <;> apply addAt_comm <;> decide

theorem execute_targets {m d l : ℕ} (U V : Label l → Vec m d)
    (x : Fin 2 → Label l) (R : Registers m d) (vs : List (Vec m d)) :
    execute U V x R (vs.map RegisterOp.target) = addAt R 2 vs.sum := by
  induction vs generalizing R with
  | nil => simp
  | cons v vs ih => simp [RegisterOp.apply, ih, addAt_addAt]

theorem sum_finRange {n : ℕ} {A : Type} [AddCommMonoid A] (f : Fin n → A) :
    ((List.finRange n).map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

def termDelta {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) : Vec m d :=
  let Q := oracle U V x (D.shift j) false 1 (oracle U V x (D.shift j) false 0 R)
  ∑ y0, ∑ y1,
    (α * D.term j ((Q 0 ⬝ᵥ V y0) + (Q 1 ⬝ᵥ V y1) - g)) • W (f y0 y1)

theorem termProgram_update {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) :
    execute U V x R (termProgram U V W D f x α g R j) =
      addAt R 2 (termDelta U V W D f x α g R j) := by
  let Q := oracle U V x (D.shift j) false 1 (oracle U V x (D.shift j) false 0 R)
  let vs : List (Vec m d) := (List.finRange (2 ^ l)).flatMap fun y0 =>
    (List.finRange (2 ^ l)).map fun y1 =>
      (α * D.term j ((Q 0 ⬝ᵥ V y0) + (Q 1 ⬝ᵥ V y1) - g)) • W (f y0 y1)
  have hvs : (termProgram U V W D f x α g R j) =
      [.query (D.shift j) false 0, .query (D.shift j) false 1] ++
      vs.map RegisterOp.target ++ [.query (-D.shift j) false 0, .query (-D.shift j) false 1] := by
    simp [termProgram, vs, Q, List.map_flatMap, List.map_map, Function.comp_def]
  rw [hvs, execute_append, execute_append]
  simp only [execute_cons, execute_nil, RegisterOp.apply]
  rw [execute_targets]
  simp only [oracle_addAt_target]
  have hrestore : oracle U V x (-D.shift j) false 1
      (oracle U V x (-D.shift j) false 0 Q) = R := by
    simp [Q, oracle, addAt_comm, addAt_addAt]
  rw [hrestore]
  congr 1
  simp [vs, List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def,
    sum_finRange, termDelta, Q]


end CatalyticTreeEval.Main


set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem matching_score_mem {m d N : ℕ} {S : Set (ZMod m)}
    {U V : Fin N → Vec m d} (h : SMatching S U V) (i j : Fin N) : U i ⬝ᵥ V j ∈ S := by
  by_cases hij : i = j
  · subst j
    rw [h.2.1.1 i]
    exact h.1
  · exact h.2.2 i j hij

theorem matching_score_eq_zero_iff {m d N : ℕ} {S : Set (ZMod m)}
    {U V : Fin N → Vec m d} (h : SMatching S U V) (i j : Fin N) :
    U i ⬝ᵥ V j = 0 ↔ i = j := by
  constructor
  · intro hz
    by_contra hij
    exact h.2.1.2 i j hij hz
  · rintro rfl
    exact h.2.1.1 i

theorem two_scores_eq_zero_iff {m d N : ℕ} {S : Set (ZMod m)}
    {U V : Fin N → Vec m d} (h : SMatching S U V) (hn : Noncancelling S)
    (x0 x1 y0 y1 : Fin N) :
    (U x0 ⬝ᵥ V y0) + (U x1 ⬝ᵥ V y1) = 0 ↔ y0 = x0 ∧ y1 = x1 := by
  constructor
  · intro hz
    obtain ⟨h0,h1⟩ := hn _ (matching_score_mem h x0 y0) _ (matching_score_mem h x1 y1) hz
    exact ⟨((matching_score_eq_zero_iff h x0 y0).1 h0).symm,
      ((matching_score_eq_zero_iff h x1 y1).1 h1).symm⟩
  · rintro ⟨h0,h1⟩
    rw [h0, h1, h.2.1.1 x0, h.2.1.1 x1, zero_add]

/-- Every incorrect candidate pair cancels, for the arbitrary mask induced by
the initial registers. Only the correct pair sees the decoder at zero. -/
theorem decoder_pair_weight (F : Frame) (hF : F.valid)
    (x : Fin 2 → Label F.l) (R : Registers F.m F.d) (y0 y1 : Label F.l) :
    (∑ j, F.D.term j
      (((R 0 + F.D.shift j • F.U (x 0)) ⬝ᵥ F.V y0) +
       ((R 1 + F.D.shift j • F.U (x 1)) ⬝ᵥ F.V y1) -
       ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1))))) =
    if y0 = x 0 ∧ y1 = x 1 then 1 else 0 := by
  rcases hF with ⟨_,_,hmatch,hn,hD,_⟩
  have expand (j : Fin F.k) :
      ((R 0 + F.D.shift j • F.U (x 0)) ⬝ᵥ F.V y0) +
       ((R 1 + F.D.shift j • F.U (x 1)) ⬝ᵥ F.V y1) -
       ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1))) =
      (((R 0 ⬝ᵥ F.V y0) + (R 1 ⬝ᵥ F.V y1)) -
       ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1)))) +
      ((F.U (x 0) ⬝ᵥ F.V y0) + (F.U (x 1) ⬝ᵥ F.V y1)) * F.D.shift j := by
    simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
    ring
  simp_rw [expand]
  by_cases hy : y0 = x 0 ∧ y1 = x 1
  · rcases hy with ⟨rfl,rfl⟩
    simpa [hmatch.2.1.1] using hD.2.2
  · rw [if_neg hy]
    apply hD.2.1
    · exact ⟨_, matching_score_mem hmatch _ _, _, matching_score_mem hmatch _ _, rfl⟩
    · intro hz
      exact hy ((two_scores_eq_zero_iff hmatch hn _ _ _ _).1 hz)

end CatalyticTreeEval.Main


set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem childOps_append {m d : ℕ} (as bs : List (RegisterOp m d)) :
    childOps (as ++ bs) = childOps as ++ childOps bs := by simp [childOps]

theorem InversePairs.append {m d : ℕ} {as bs : List (RegisterOp m d)}
    (ha : InversePairs as) (hb : InversePairs bs) : InversePairs (as ++ bs) := by
  classical
  obtain ⟨pa, hia, hfa, hva⟩ := ha
  obtain ⟨pb, hib, hfb, hvb⟩ := hb
  let A := childOps as
  let B := childOps bs
  let e : Fin A.length ⊕ Fin B.length ≃ Fin (childOps (as ++ bs)).length :=
    finSumFinEquiv.trans (finCongr (by simp [A, B, childOps])).symm
  let ps := Equiv.sumCongr pa pb
  let p := e.permCongr ps
  have evalA (i : Fin A.length) : (childOps (as ++ bs)).get (e (.inl i)) = A.get i := by
    have hv : (e (.inl i)).val = i.val := rfl
    simpa only [List.get_eq_getElem, hv, childOps_append] using
      (List.getElem_append_left (as := A) (bs := B) i.isLt)
  have evalB (i : Fin B.length) : (childOps (as ++ bs)).get (e (.inr i)) = B.get i := by
    have hv : (e (.inr i)).val = A.length + i.val := rfl
    simpa only [List.get_eq_getElem, hv, childOps_append, Nat.add_comm] using
      (List.getElem_append_right' A i.isLt).symm
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    cases i with
    | inl a => simp [p, ps, Equiv.permCongr_apply, hia a]
    | inr b => simp [p, ps, Equiv.permCongr_apply, hib b]
  · intro i h
    obtain ⟨i,rfl⟩ := e.surjective i
    cases i with
    | inl a =>
        have he := e.injective h
        exact hfa a (by simpa [p, ps, Equiv.permCongr_apply] using he)
    | inr b =>
        have he := e.injective h
        exact hfb b (by simpa [p, ps, Equiv.permCongr_apply] using he)
  · intro i
    obtain ⟨i,rfl⟩ := e.surjective i
    cases i with
    | inl a =>
        simp only [p, Equiv.permCongr_apply, Equiv.symm_apply_apply, ps, Equiv.sumCongr_apply,
          Sum.map_inl, evalA]
        exact hva a
    | inr b =>
        simp only [p, Equiv.permCongr_apply, Equiv.symm_apply_apply, ps, Equiv.sumCongr_apply,
          Sum.map_inr, evalB]
        exact hvb b

private def queryPairPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem queryPairPerm_involutive : Function.Involutive queryPairPerm := by
  unfold Function.Involutive
  decide

private theorem queryPairPerm_noFixed : ∀ i, queryPairPerm i ≠ i := by decide

theorem queryBlock_inversePairs {m d : ℕ} (b : ZMod m) (ctrl : Bool) :
    InversePairs ([.query b ctrl 0, .query b ctrl 1,
      .query (-b) ctrl 0, .query (-b) ctrl 1] : List (RegisterOp m d)) := by
  unfold InversePairs
  dsimp [childOps]
  refine ⟨queryPairPerm, queryPairPerm_involutive, queryPairPerm_noFixed, ?_⟩
  intro i
  fin_cases i
  · rfl
  · rfl
  · change RegisterOp.query b ctrl 0 = RegisterOp.query (-(-b)) ctrl 0
    simp
  · change RegisterOp.query b ctrl 1 = RegisterOp.query (-(-b)) ctrl 1
    simp

theorem childOps_targets {m d : ℕ} (vs : List (Vec m d)) :
    childOps (vs.map RegisterOp.target) = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [childOps] using ih

theorem termProgram_childOps {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) :
    childOps (termProgram U V W D f x α g R j) =
      [.query (D.shift j) false 0, .query (D.shift j) false 1,
       .query (-D.shift j) false 0, .query (-D.shift j) false 1] := by
  simp [termProgram, childOps, List.filter_flatMap, List.filter_map]

theorem termProgram_inversePairs {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) :
    InversePairs (termProgram U V W D f x α g R j) := by
  unfold InversePairs
  rw [termProgram_childOps]
  have h := queryBlock_inversePairs (d := d) (D.shift j) false
  dsimp [InversePairs, childOps] at h
  exact h

theorem accumulate_inversePairs {m d l : ℕ} {J : Type}
    (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (mk : Registers m d → J → List (RegisterOp m d)) (js : List J)
    (hmk : ∀ R j, InversePairs (mk R j))
    (acc : Registers m d × List (RegisterOp m d)) (hacc : InversePairs acc.2) :
    InversePairs (js.foldl (fun acc j => let ops := mk acc.1 j
      (execute U V x acc.1 ops, acc.2 ++ ops)) acc).2 := by
  induction js generalizing acc with
  | nil => exact hacc
  | cons j js ih =>
      apply ih
      exact hacc.append (hmk _ _)

theorem oneLevelProgram_inversePairs {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α : ZMod m) (R : Registers m d) :
    InversePairs (oneLevelProgram U V W D f x α R) := by
  unfold oneLevelProgram
  apply accumulate_inversePairs
  · intro Q j
    exact termProgram_inversePairs U V W D f x α _ Q j
  · exact innerProgram_inversePairs U V x R

end CatalyticTreeEval.Main


set_option autoImplicit false

namespace CatalyticTreeEval.Main

theorem termDelta_target {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (j : Fin k) (v : Vec m d) :
    termDelta U V W D f x α g (addAt R 2 v) j = termDelta U V W D f x α g R j := by
  simp [termDelta, oracle]

theorem termDelta_sum (F : Frame) (hF : F.valid)
    (W : Label F.l → Vec F.m F.d) (f : Label F.l → Label F.l → Label F.l)
    (x : Fin 2 → Label F.l) (α : ZMod F.m) (R : Registers F.m F.d) :
    (∑ j, termDelta F.U F.V W F.D f x α
      ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1))) R j) =
      α • W (f (x 0) (x 1)) := by
  have expand (j : Fin F.k) :
      termDelta F.U F.V W F.D f x α
        ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1))) R j =
      ∑ y0, ∑ y1, (α * F.D.term j
        (((R 0 + F.D.shift j • F.U (x 0)) ⬝ᵥ F.V y0) +
         ((R 1 + F.D.shift j • F.U (x 1)) ⬝ᵥ F.V y1) -
         ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1))))) • W (f y0 y1) := by
    simp [termDelta, oracle]
  simp_rw [expand]
  rw [Finset.sum_comm]
  calc
    _ = ∑ y0, ∑ y1, (α * (∑ j, F.D.term j
        (((R 0 + F.D.shift j • F.U (x 0)) ⬝ᵥ F.V y0) +
         ((R 1 + F.D.shift j • F.U (x 1)) ⬝ᵥ F.V y1) -
         ((R 0 ⬝ᵥ F.V (x 0)) + (R 1 ⬝ᵥ F.V (x 1)))))) • W (f y0 y1) := by
      apply Finset.sum_congr rfl
      intro y0 _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y1 _
      rw [Finset.mul_sum, Finset.sum_smul]
    _ = α • W (f (x 0) (x 1)) := by
      simp_rw [decoder_pair_weight F hF]
      simp [ite_and]

theorem execute_accumulate {m d l : ℕ} {J : Type}
    (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (mk : Registers m d → J → List (RegisterOp m d)) (js : List J)
    (R : Registers m d) (acc : Registers m d × List (RegisterOp m d))
    (hacc : execute U V x R acc.2 = acc.1) :
    execute U V x R
      (js.foldl (fun acc j => let ops := mk acc.1 j
        (execute U V x acc.1 ops, acc.2 ++ ops)) acc).2 =
      (js.foldl (fun acc j => let ops := mk acc.1 j
        (execute U V x acc.1 ops, acc.2 ++ ops)) acc).1 := by
  induction js generalizing acc with
  | nil => exact hacc
  | cons j js ih =>
      apply ih
      simp only [execute_append, hacc]

theorem accumulate_fst {m d l : ℕ} {J : Type}
    (U V : Label l → Vec m d) (x : Fin 2 → Label l)
    (mk : Registers m d → J → List (RegisterOp m d)) (js : List J)
    (acc : Registers m d × List (RegisterOp m d)) :
    (js.foldl (fun acc j => let ops := mk acc.1 j
      (execute U V x acc.1 ops, acc.2 ++ ops)) acc).1 =
      js.foldl (fun R j => execute U V x R (mk R j)) acc.1 := by
  induction js generalizing acc with
  | nil => rfl
  | cons j js ih => simpa only [List.foldl_cons] using
      (ih (execute U V x acc.1 (mk acc.1 j), acc.2 ++ mk acc.1 j))

theorem term_fold {m d l k : ℕ} (U V W : Label l → Vec m d) (D : Decoder m k)
    (f : Label l → Label l → Label l) (x : Fin 2 → Label l)
    (α g : ZMod m) (R : Registers m d) (js : List (Fin k)) (v : Vec m d) :
    js.foldl (fun Q j => execute U V x Q (termProgram U V W D f x α g Q j)) (addAt R 2 v) =
      addAt R 2 (v + (js.map (termDelta U V W D f x α g R)).sum) := by
  induction js generalizing v with
  | nil => simp
  | cons j js ih =>
      rw [List.foldl_cons]
      conv_lhs =>
        arg 2
        rw [termProgram_update, termDelta_target, addAt_addAt]
      rw [ih]
      simp only [List.map_cons, List.sum_cons, add_assoc]

theorem oneLevelProgram_update (F : Frame) (hF : F.valid)
    (W : Label F.l → Vec F.m F.d) (f : Label F.l → Label F.l → Label F.l)
    (x : Fin 2 → Label F.l) (α : ZMod F.m) (R : Registers F.m F.d) :
    execute F.U F.V x R (oneLevelProgram F.U F.V W F.D f x α R) =
      addAt R 2 (α • W (f (x 0) (x 1))) := by
  unfold oneLevelProgram
  rw [execute_accumulate F.U F.V x
    (fun Q j => termProgram F.U F.V W F.D f x α (innerProgram F.U F.V x R).1 Q j)
    (List.finRange F.k) R _ rfl]
  rw [accumulate_fst]
  simp only [innerProgram_value, innerProgram_restores]
  conv_lhs =>
    arg 2
    rw [← addAt_zero R 2]
  rw [term_fold]
  simp only [zero_add, sum_finRange, termDelta_sum F hF]

theorem oneLevelProgram_algebra (F : Frame) (hF : F.valid)
    (W : Label F.l → Vec F.m F.d) (f : Label F.l → Label F.l → Label F.l)
    (x : Fin 2 → Label F.l) (α : ZMod F.m) (R : Registers F.m F.d) :
    execute F.U F.V x R (oneLevelProgram F.U F.V W F.D f x α R) =
      addAt R 2 (α • W (f (x 0) (x 1))) ∧
    InversePairs (oneLevelProgram F.U F.V W F.D f x α R) :=
  ⟨oneLevelProgram_update F hF W f x α R,
    oneLevelProgram_inversePairs F.U F.V W F.D f x α R⟩

end CatalyticTreeEval.Main

open CatalyticTreeEval.Main

theorem solution (F : Frame) (hF : F.valid)
    (W : Label F.l → Vec F.m F.d) (f : Label F.l → Label F.l → Label F.l)
    (x : Fin 2 → Label F.l) (α : ZMod F.m) (R : Registers F.m F.d) :
    execute F.U F.V x R (oneLevelProgram F.U F.V W F.D f x α R) =
      addAt R 2 (α • W (f (x 0) (x 1))) ∧
    InversePairs (oneLevelProgram F.U F.V W F.D f x α R) :=
  oneLevelProgram_algebra F hF W f x α R
