-- Prove2me | solution 1 for FixedMachinePrec.marked_slots_state_path
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:10:44.880687+00:00
-- url     : https://prove2.me/submissions/c99a367a-10ad-4c9b-8dd7-e6ede3399cfc

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy


open FixedMachinePrec


private theorem union_mem {N} (s : List (Finset (Fin N))) (x) : x ∈ unionSlots s ↔ ∃ A ∈ s, x ∈ A := by
  unfold unionSlots; induction s with | nil => simp | cons A s ih => simp [ih]

private theorem slot_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) {i} (hi : i < s.length) {x} (hx : x ∈ s[i]) : localTime s x = i+1 := by
  unfold localTime
  congr 1
  apply (List.findIdx_eq hi).mpr
  refine ⟨decide_eq_true hx,?_⟩
  intro j hj; simp only [decide_eq_false_iff_not]
  exact fun h => Finset.disjoint_left.mp (List.pairwise_iff_getElem.mp hd j i (hj.trans hi) hi hj) h hx

private theorem location {N} {s : List (Finset (Fin N))} {x} (hx : x ∈ unionSlots s) :
    ∃ (i : ℕ) (hi : i < s.length), x ∈ s[i] := by
  obtain ⟨A,hA,hx⟩ := (union_mem _ _).mp hx
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hA
  exact ⟨i,hi,hx⟩

private theorem enumerate {N} (A : Finset (Fin N)) : ∃ k < 2^N, decodeSet N k = A := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0,by positivity,by simp [decodeSet]⟩
  | insert a A _ ih =>
    obtain ⟨k,hk,rfl⟩ := ih
    refine ⟨2^a.val ||| k,Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) a.isLt) hk,?_⟩
    ext x; simp [decodeSet,Nat.testBit_two_pow,Fin.ext_iff]; tauto

private theorem codes {N} (F : Finset (Finset (Fin N))) (A) : A ∈ listByCode F ↔ A ∈ F := by
  simp only [listByCode,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨k,hk,e⟩; split at e <;> simp_all
  · intro h; obtain ⟨k,hk,he⟩ := enumerate A; exact ⟨k,hk,by simp [he,h]⟩

private theorem subsets_spec {N m : ℕ} (A : Finset (Fin N)) : A ∈ mSubsetsLex N m ↔ A.card = m := by
  classical
  simp only [mSubsetsLex, List.mem_map, List.mem_mergeSort, List.mem_sublistsLen]
  constructor
  · rintro ⟨l,⟨hsub,hlen⟩,rfl⟩
    rw [List.toFinset_card_of_nodup ((List.nodup_finRange N).sublist hsub), hlen]
  · intro h
    let l := (List.finRange N).filter (fun x => decide (x ∈ A))
    have he : l.toFinset = A := by ext x; simp [l]
    have hd : l.Nodup := (List.nodup_finRange N).filter _
    exact ⟨l,⟨List.filter_sublist,by rwa [← List.toFinset_card_of_nodup hd, he]⟩,he⟩
private theorem between_mem {N} {S : List (Finset (Fin N))} (hd : S.Pairwise Disjoint) (a b x) :
    x ∈ slotsBetween S a b ↔ x ∈ unionSlots S ∧ a < localTime S x ∧ localTime S x < b := by
  simp only [slotsBetween,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨i,⟨hi,ha,hb⟩,hx⟩
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi] at hx
    exact ⟨(union_mem _ _).mpr ⟨_,List.getElem_mem hi,hx⟩,slot_time hd hi hx ▸ ha,slot_time hd hi hx ▸ hb⟩
  · rintro ⟨hu,ha,hb⟩; obtain ⟨i,hi,hx⟩ := location hu
    exact ⟨i,⟨hi,slot_time hd hi hx ▸ ha,slot_time hd hi hx ▸ hb⟩,by simpa [List.getD_eq_getElem?_getD,hi] using hx⟩

private theorem interval_divides {N m} {p : Fin N → Fin N → Prop} {W S} (hs : IsFullSchedule p m W S) (a b) : m ∣ (slotsBetween S a b).card := by
  let Z := (S.drop a).take (b-1-a)
  have mid : unionSlots Z = slotsBetween S a b := by
    ext x; rw [union_mem]; simp only [slotsBetween,Finset.mem_biUnion,Finset.mem_filter,Finset.mem_range]
    constructor
    · rintro ⟨A,hA,hx⟩; obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hA
      have len : j < min (b-1-a) (S.length-a) := by simpa [Z] using hj
      refine ⟨a+j,⟨by omega,by omega,by omega⟩,?_⟩
      simpa [Z,List.getD_eq_getElem?_getD,show a+j < S.length by omega] using hx
    · rintro ⟨i,⟨hi,ha,hb⟩,hx⟩
      have hj : i-a < Z.length := by simp [Z];omega
      refine ⟨Z[i-a],List.getElem_mem hj,?_⟩
      simpa [Z,show a+(i-a) = i by omega,List.getD_eq_getElem?_getD,hi] using hx
  have count (l : List (Finset (Fin N))) (hd : l.Pairwise Disjoint) (ha : ∀ A ∈ l, A.card = m) : (unionSlots l).card = m*l.length := by
    induction l with
    | nil => simp [unionSlots]
    | cons A l ih =>
      obtain ⟨hdis,hd'⟩ := List.pairwise_cons.mp hd
      have dj : Disjoint A (unionSlots l) := by
        apply Finset.disjoint_left.mpr; intro x hx hy; obtain ⟨B,hB,hxB⟩ := (union_mem _ _).mp hy
        exact Finset.disjoint_left.mp (hdis _ hB) hx hxB
      change (A ∪ unionSlots l).card = _
      rw [Finset.card_union_of_disjoint dj,ha _ (by simp),ih hd' (fun B hB => ha _ (by simp [hB]))]; simp [Nat.mul_add,Nat.add_comm]
  rw [← mid]
  exact ⟨Z.length,count Z hs.2.1.drop.take (fun A h => (hs.1 _ ((List.drop_sublist _ _).subset ((List.take_sublist _ _).subset h))).1)⟩

private theorem adjacent {α : Type*} (R : α → α → Prop) (l : List α) (h : ∀ ab ∈ l.zip l.tail, R ab.1 ab.2) : l.IsChain R := by
  cases l with
  | nil => simp
  | cons a l =>
    induction l generalizing a with
    | nil => simp
    | cons b l ih => exact List.isChain_cons_cons.mpr ⟨h (a,b) (by simp),ih b (fun ab hab => h ab (by exact List.mem_cons_of_mem _ hab))⟩

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
(tab : Table N) (hg : ∀ A ∈ gaps S marks, (lookup F tab A).isSome = true) :
    let st := buildStates prec m C W
    let lk := fun X => (lookup F tab X).isSome
    ∃ i t a b, st[i]? = some a ∧ st[t]? = some b ∧ lk a.L = true ∧ lk b.R = true ∧
      Relation.ReflTransGen (fun x y => edge st lk x y = true) i t := by
  classical
  let st := buildStates prec m C W
  let lk := fun X => (lookup F tab X).isSome
  let L := fun t => slotsBetween S 0 t
  let Z := fun t => S.getD (t-1) ∅
  let recd (t) : StateRec N := ⟨L t,Z t,W \ (L t ∪ Z t)⟩
  have hu : unionSlots S = W := hs.2.2.1
  have loc {x} (hx : x ∈ W) := location (hu ▸ hx)
  have span {x} (hx : x ∈ W) : 1 ≤ localTime S x ∧ localTime S x ≤ S.length := by
    obtain ⟨i,hi,h⟩ := loc hx; rw [slot_time hs.2.1 hi h]; omega
  have lm (t x) : x ∈ L t ↔ x ∈ W ∧ localTime S x < t := by simp [L,between_mem hs.2.1,hu,localTime]
  have zm (t) (ht : t ∈ marks) (x) : x ∈ Z t ↔ x ∈ W ∧ localTime S x = t := by
    obtain ⟨lo,hi⟩ := hr t ht
    have k : t-1 < S.length := by omega
    simp only [Z,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem k,Option.getD_some]
    constructor
    · intro h; exact ⟨hu ▸ (union_mem _ _).mpr ⟨_,List.getElem_mem k,h⟩,(slot_time hs.2.1 k h).trans (by omega)⟩
    · rintro ⟨hx,he⟩; obtain ⟨i,hi,h⟩ := loc hx; have ht := slot_time hs.2.1 hi h
      simpa only [show i=t-1 by omega] using h
  have inc {x y} (hx : x ∈ W) (hy : y ∈ W) (h : prec x y) : localTime S x < localTime S y := by
    obtain ⟨i,hi,hx'⟩ := loc hx; obtain ⟨j,hj,hy'⟩ := loc hy
    rw [slot_time hs.2.1 hi hx',slot_time hs.2.1 hj hy']; exact Nat.succ_lt_succ (hs.2.2.2 _ _ hi hj _ _ hx' hy' h)
  have rem (t) (ht : t ∈ marks) : (recd t).R = slotsBetween S t (S.length+1) := by
    ext x; simp only [recd,Finset.mem_sdiff,Finset.mem_union,lm,zm t ht,between_mem hs.2.1,hu]; by_cases hx : x ∈ W <;> simp [hx] <;> have := span hx <;> omega
  have record_exists (t) (ht : t ∈ marks) : ∃ i : ℕ, st[i]? = some (recd t) := by
    obtain ⟨cut,hcut,eq⟩ := hc t ht
    change L t = W ∩ cut at eq
    have k : t-1 < S.length := by have := hr t ht; omega
    have good := hs.1 _ (List.getElem_mem k)
    have ze : Z t = S[t-1] := by simp [Z,List.getD_eq_getElem?_getD,k]
    rw [← ze] at good
    have hslot : Z t ⊆ W \ L t := by intro x hx; obtain ⟨hx,he⟩ := (zm t ht x).mp hx; simp [lm,hx,he]
    have il : ∀ x ∈ L t, ∀ y ∈ W, prec y x → y ∈ L t := by
      intro x hx y hy h; obtain ⟨hw,ht⟩ := (lm t x).mp hx; exact (lm t y).mpr ⟨hy,(inc hy hw h).trans ht⟩
    have iz : ∀ x ∈ L t ∪ Z t, ∀ y ∈ W, prec y x → y ∈ L t ∪ Z t := by
      intro x hx y hy h; apply Finset.mem_union_left
      rcases Finset.mem_union.mp hx with l|z
      · exact il _ l _ hy h
      · obtain ⟨hw,e⟩ := (zm t ht x).mp z; exact (lm t y).mpr ⟨hy,e ▸ inc hy hw h⟩
    have hR : m ∣ (W \ (L t ∪ Z t)).card := by change m ∣ (recd t).R.card; rw [rem t ht]; exact interval_divides hs t (S.length+1)
    have hin : recd t ∈ st := by
      apply List.mem_flatMap.mpr; refine ⟨cut,(codes C _).mpr hcut,?_⟩
      dsimp only; rw [← eq,if_pos (interval_divides hs 0 t)]
      apply List.mem_filterMap.mpr
      exact ⟨Z t,List.mem_filter.mpr ⟨(subsets_spec _).mpr good.1,decide_eq_true hslot⟩,by simp only [if_pos (And.intro hR (And.intro good.2 (And.intro il iz)))];rfl⟩
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hin
    exact ⟨i,by simp [hi,he]⟩
  let index (t : ℕ) := if h : t ∈ marks then (record_exists t h).choose else 0
  have atIndex t (ht : t ∈ marks) : st[index t]? = some (recd t) := by simpa [index,ht] using (record_exists t ht).choose_spec
  let gapOK (a b : ℕ) := lk (slotsBetween S a b) = true
  have path : (0 :: marks ++ [S.length+1]).IsChain gapOK := adjacent _ _ (fun ab h => hg _ (List.mem_map.mpr ⟨ab,h,rfl⟩))
  let E := fun i j => edge st lk i j = true
  have link (a b) (ha : a ∈ marks) (hb : b ∈ marks) (lt : a < b) (ok : gapOK a b) : E (index a) (index b) := by
    have sub : L a ∪ Z a ⊆ L b := by
      intro x hx; simp only [Finset.mem_union,lm,zm a ha] at hx; apply (lm _ _).mpr; grind
    have diff : L b \ (L a ∪ Z a) = slotsBetween S a b := by
      ext x; simp only [Finset.mem_sdiff,Finset.mem_union,lm,zm a ha,between_mem hs.2.1,hu]; by_cases hx : x ∈ W <;> simp [hx] <;> omega
    simp only [E,edge,atIndex _ ha,atIndex _ hb,recd,decide_eq_true sub,Bool.true_and,diff];exact ok
  have walk (a : ℕ) (tail : List ℕ) (am : a ∈ marks) (hm' : ∀ b ∈ tail, b ∈ marks)
      (ord : (a::tail).Pairwise (· < ·)) (pass : (a::tail ++ [S.length+1]).IsChain gapOK) :
      ∃ b ∈ marks, lk (recd b).R = true ∧ Relation.ReflTransGen E (index a) (index b) := by
    induction tail generalizing a with
    | nil => exact ⟨a,am,rem a am ▸ (List.isChain_cons_cons.mp pass).1,.refl⟩
    | cons b l ih =>
      have bm := hm' b (by simp)
      obtain ⟨z,hz,hR,hpath⟩ := ih b bm (fun c h => hm' c (by simp [h])) (List.pairwise_cons.mp ord).2 (List.isChain_cons_cons.mp pass).2
      exact ⟨z,hz,hR,hpath.head (link a b am bm ((List.pairwise_cons.mp ord).1 b (by simp)) (List.isChain_cons_cons.mp pass).1)⟩
  cases he : marks with
  | nil => contradiction
  | cons a tail =>
    rw [he] at path hi
    obtain ⟨z,hz,hR,hpath⟩ := walk a tail (by simp [he]) (fun b h => he ▸ List.mem_cons_of_mem _ h) hi (List.isChain_cons_cons.mp path).2
    exact ⟨index a,index z,recd a,recd z,atIndex _ (by simp [he]),atIndex _ hz,(List.isChain_cons_cons.mp path).1,hR,hpath⟩
