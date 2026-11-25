-- Prove2me | solution 3 for DetDLP.factor_splitting_driver_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:26:33.896683+00:00
-- url     : https://prove2.me/submissions/ce47c303-6797-4aab-8d9b-95603898db97

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_M89_MachineComp
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Definitions.Def_ToTuring_Lib_Nat1
import Theorems.Thm_Groundwork_PolyT_div
import Theorems.Thm_Groundwork_PolyT_mod

set_option autoImplicit false

namespace DetDLP.FactorSplittingDriver

open Groundwork Groundwork.PolyT
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

attribute [local fun_prop] Groundwork.PolyT.comp
attribute [local fun_prop] Groundwork.PolyT.const
attribute [local fun_prop] Groundwork.PolyT.fst
attribute [local fun_prop] Groundwork.PolyT.optionElim
attribute [local fun_prop] Groundwork.PolyT.prodMk
attribute [local fun_prop] Groundwork.PolyT.snd
attribute [local fun_prop] Groundwork.PolyT.sumElim
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.div
attribute [local fun_prop] Groundwork.PolyT.mod
attribute [local fun_prop] P2M_Groundwork_PolyT_cond__4c673073da15
attribute [local fun_prop] P2M_Groundwork_PolyT_cons__3a60f43a3b86
attribute [local fun_prop] P2M_Groundwork_PolyT_id__1c5d0f44cc8f
attribute [local fun_prop] P2M_Groundwork_PolyT_ite__226169acf219

/-! ## Section 1: Pairing, List-of-Nat Codec, Sorting, and DFS `PolyT` Step Function -/

def pairWord (x y : List Bool) : List Bool :=
  x.flatMap (fun b => [true, b]) ++ [false] ++ y

theorem pairWord_length (x y : List Bool) :
    (pairWord x y).length = 2 * x.length + 1 + y.length := by
  have hl : (x.flatMap (fun b => [true, b])).length = 2 * x.length := by
    induction x with
    | nil => simp
    | cons _ _ ih => simp [ih]; omega
  simp only [pairWord, List.length_append, List.length_singleton, hl]

@[fun_prop] theorem pairWord_poly {α : Type} [Enc α] {x y : α → List Bool}
    (hx : PolyT x) (hy : PolyT y) : PolyT (fun a => pairWord (x a) (y a)) := by
  unfold pairWord
  fun_prop

def unpairStep (s : Bool × Bool × List Bool × List Bool) (b : Bool) :
    Bool × Bool × List Bool × List Bool :=
  if s.1 then (true, false, s.2.2.1, b :: s.2.2.2)
  else if s.2.1 then (false, false, b :: s.2.2.1, s.2.2.2)
  else if b then (false, true, s.2.2.1, s.2.2.2)
  else (true, false, s.2.2.1, s.2.2.2)

def unpairWord (w : List Bool) : List Bool × List Bool :=
  let r := w.foldl unpairStep (false, false, [], [])
  (r.2.2.1.reverse, r.2.2.2.reverse)

private theorem unpairStep_len (s : Bool × Bool × List Bool × List Bool) (b : Bool) :
    len (unpairStep s b) ≤ len s + 3 := by
  rcases s with ⟨inY, expB, rx, ry⟩
  cases inY <;> cases expB <;> cases b <;>
    simp [unpairStep, len_pair, len_bool, len_cons] <;> omega

@[fun_prop] theorem unpairWord_poly {α : Type} [Enc α] {w : α → List Bool}
    (hw : PolyT w) : PolyT (fun a => unpairWord (w a)) := by
  have hstep : PolyT fun p : α × (Bool × Bool × List Bool × List Bool) × Bool =>
      unpairStep p.2.1 p.2.2 := by
    unfold unpairStep
    fun_prop
  have hfold : PolyT fun a => (w a).foldl unpairStep (false, false, [], []) := by
    refine Groundwork.PolyT.foldl_add hw (by fun_prop) hstep
      ⟨fun _ => 3, Groundwork.PB.const 3, fun _ c e _ => unpairStep_len c e⟩
  unfold unpairWord
  fun_prop

private theorem foldl_unpair_pairs (x rx ry : List Bool) :
    (x.flatMap (fun b => [true, b])).foldl unpairStep (false, false, rx, ry) =
      (false, false, x.reverse ++ rx, ry) := by
  induction x generalizing rx with
  | nil => simp
  | cons a x ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
    have h1 : unpairStep (false, false, rx, ry) true = (false, true, rx, ry) := rfl
    have h2 : unpairStep (false, true, rx, ry) a = (false, false, a :: rx, ry) := by
      cases a <;> rfl
    rw [h1, h2, ih (a :: rx)]
    simp

private theorem foldl_unpair_y (y rx ry : List Bool) :
    y.foldl unpairStep (true, false, rx, ry) = (true, false, rx, y.reverse ++ ry) := by
  induction y generalizing ry with
  | nil => simp
  | cons a y ih =>
    simp only [List.foldl_cons]
    have h1 : unpairStep (true, false, rx, ry) a = (true, false, rx, a :: ry) := rfl
    rw [h1, ih (a :: ry)]
    simp

@[simp] theorem unpairWord_pairWord (x y : List Bool) :
    unpairWord (pairWord x y) = (x, y) := by
  unfold unpairWord pairWord
  rw [List.foldl_append, List.foldl_append, foldl_unpair_pairs, List.foldl_cons, List.foldl_nil]
  have hsep : unpairStep (false, false, x.reverse ++ [], ([] : List Bool)) false =
      (true, false, x.reverse, []) := by simp [unpairStep]
  rw [hsep, foldl_unpair_y]
  simp

theorem frame_eq_flatMap (bits : List Bool) :
    Encoding.frame bits = bits.flatMap (fun b => [true, b]) ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    simp only [Encoding.frame] at ih ⊢
    rw [List.foldr_cons, List.flatMap_cons, ih]
    rfl

theorem frame_length (bits : List Bool) :
    (Encoding.frame bits).length = 2 * bits.length + 1 := by
  rw [frame_eq_flatMap, List.length_append, List.length_singleton]
  have hl : (bits.flatMap (fun b => [true, b])).length = 2 * bits.length := by
    induction bits with
    | nil => simp
    | cons _ _ ih => simp [ih]; omega
  rw [hl]

theorem encodeList_eq_flatMap {α : Type*} (enc : α → List Bool) (xs : List α) :
    Encoding.encodeList enc xs =
      xs.flatMap (fun a => true :: Encoding.frame (enc a)) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [Encoding.encodeList, ih, List.flatMap_cons, List.cons_append, List.append_assoc]

theorem encodeNatListBin_length (xs : List ℕ) :
    (encodeNatListBin xs).length =
      2 * (xs.map (fun a => (countWord a).length)).sum + 2 * xs.length + 1 := by
  unfold encodeNatListBin
  induction xs with
  | nil => simp [Encoding.encodeList]
  | cons a as ih =>
    simp only [Encoding.encodeList, List.length_cons, List.length_append, frame_length,
      List.map_cons, List.sum_cons] at ih ⊢
    omega

@[fun_prop] theorem countWord_poly {α : Type} [Enc α] {f : α → ℕ}
    (hf : PolyT f) : PolyT (fun a => countWord (f a)) := by
  have h : PolyT (fun a => if f a ≤ 0 then [false] else (f a).bits) := by fun_prop
  refine h.congr fun a => ?_
  unfold countWord
  congr 1
  simp

@[fun_prop] theorem encodeNatListBin_poly {α : Type} [Enc α] {l : α → List ℕ}
    (hl : PolyT l) : PolyT (fun a => encodeNatListBin (l a)) := by
  have h : PolyT (fun a => (l a).flatMap (fun n =>
      true :: ((countWord n).flatMap (fun b => [true, b]) ++ [false])) ++ [false]) := by
    fun_prop
  refine h.congr fun a => ?_
  unfold encodeNatListBin
  rw [encodeList_eq_flatMap]
  congr 1
  refine List.flatMap_congr fun n _ => ?_
  rw [frame_eq_flatMap]

theorem bval_countWord (a : ℕ) : bval (countWord a) = a := by
  unfold countWord
  split_ifs with ha
  · subst ha; rfl
  · exact bval_bits a

theorem countWord_ne_nil (a : ℕ) : countWord a ≠ [] := by
  unfold countWord
  split_ifs with ha
  · simp
  · intro h
    exact ha (eq_zero_of_bits_eq_nil h)

theorem countWord_isEmpty_false (a : ℕ) : (countWord a).isEmpty = false := by
  cases h : countWord a with
  | nil => exact absurd h (countWord_ne_nil a)
  | cons _ _ => rfl

def decStep (s : Bool × Bool × Bool × List Bool × List ℕ) (b : Bool) :
    Bool × Bool × Bool × List Bool × List ℕ :=
  if s.1 then s
  else if !s.2.1 then
    if b then (false, true, false, [], s.2.2.2.2)
    else (true, false, false, [], s.2.2.2.2)
  else if s.2.2.1 then (false, true, false, b :: s.2.2.2.1, s.2.2.2.2)
  else if b then (false, true, true, s.2.2.2.1, s.2.2.2.2)
  else (false, false, false, [], bval s.2.2.2.1.reverse :: s.2.2.2.2)

def decNatList (w : List Bool) : List ℕ :=
  (w.foldl decStep (false, false, false, [], [])).2.2.2.2.reverse

private theorem len_bval_le (w : List Bool) : len (bval w) ≤ len w := by
  rw [len_nat, ← Nat.size_eq_bits_len, bits_bval, len_bools]
  have h := length_bitsTrim_le w
  omega

private theorem decStep_len (s : Bool × Bool × Bool × List Bool × List ℕ) (b : Bool) :
    len (decStep s b) ≤ len s + 4 := by
  rcases s with ⟨dn, inf, expB, rc, ra⟩
  have hb : len (bval rc.reverse) ≤ len rc := by
    refine le_trans (len_bval_le rc.reverse) ?_
    simp [len_bools]
  cases dn <;> cases inf <;> cases expB <;> cases b <;>
    simp [decStep, len_pair, len_bool, len_cons, len_nil] <;> omega

@[fun_prop] theorem decNatList_poly {α : Type} [Enc α] {w : α → List Bool}
    (hw : PolyT w) : PolyT (fun a => decNatList (w a)) := by
  have hstep : PolyT fun p : α × (Bool × Bool × Bool × List Bool × List ℕ) × Bool =>
      decStep p.2.1 p.2.2 := by
    unfold decStep
    fun_prop
  have hfold : PolyT fun a => (w a).foldl decStep (false, false, false, [], []) := by
    refine Groundwork.PolyT.foldl_add hw (by fun_prop) hstep
      ⟨fun _ => 4, Groundwork.PB.const 4, fun _ c e _ => decStep_len c e⟩
  unfold decNatList
  fun_prop

private theorem foldl_decStep_frame (bits rc : List Bool) (ra : List ℕ) :
    (Encoding.frame bits).foldl decStep (false, true, false, rc, ra) =
      (false, false, false, [], bval (rc.reverse ++ bits) :: ra) := by
  induction bits generalizing rc with
  | nil =>
    simp [Encoding.frame, decStep]
  | cons b bs ih =>
    simp only [Encoding.frame] at ih ⊢
    rw [List.foldr_cons, List.foldl_cons, List.foldl_cons]
    have h1 : decStep (false, true, false, rc, ra) true = (false, true, true, rc, ra) := rfl
    have h2 : decStep (false, true, true, rc, ra) b = (false, true, false, b :: rc, ra) := by
      cases b <;> rfl
    rw [h1, h2, ih (b :: rc)]
    simp

private theorem foldl_decStep_encodeList (xs ra : List ℕ) :
    (encodeNatListBin xs).foldl decStep (false, false, false, [], ra) =
      (true, false, false, [], xs.reverse ++ ra) := by
  induction xs generalizing ra with
  | nil =>
    simp [encodeNatListBin, Encoding.encodeList, decStep]
  | cons a as ih =>
    unfold encodeNatListBin at ih ⊢
    simp only [Encoding.encodeList, List.foldl_cons, List.foldl_append]
    have h1 : decStep (false, false, false, [], ra) true = (false, true, false, [], ra) := rfl
    rw [h1, foldl_decStep_frame, List.reverse_nil, List.nil_append, bval_countWord, ih (a :: ra)]
    simp

@[simp] theorem decNatList_encodeNatListBin (xs : List ℕ) :
    decNatList (encodeNatListBin xs) = xs := by
  unfold decNatList
  rw [foldl_decStep_encodeList]
  simp

def encState (work acc : List ℕ) : List Bool :=
  pairWord (encodeNatListBin work) (encodeNatListBin acc)

def decState (s : List Bool) : List ℕ × List ℕ :=
  let p := unpairWord s
  (decNatList p.1, decNatList p.2)

@[fun_prop] theorem encState_poly {α : Type} [Enc α] {w a : α → List ℕ}
    (hw : PolyT w) (ha : PolyT a) : PolyT (fun x => encState (w x) (a x)) := by
  unfold encState
  fun_prop

@[fun_prop] theorem decState_poly {α : Type} [Enc α] {s : α → List Bool}
    (hs : PolyT s) : PolyT (fun x => decState (s x)) := by
  unfold decState
  fun_prop

@[simp] theorem decState_encState (work acc : List ℕ) :
    decState (encState work acc) = (work, acc) := by
  simp [decState, encState]

def insertStep (acc : List ℕ) (x : ℕ) : List ℕ :=
  acc.filter (· ≤ x) ++ [x] ++ acc.filter (x < ·)

def insertionSort (l : List ℕ) : List ℕ :=
  l.foldl insertStep []

private theorem len_append_nat (u v : List ℕ) :
    len (u ++ v) + 2 = len u + len v := by
  induction u with
  | nil => simp [len_nil]; omega
  | cons a u ih => simp only [List.cons_append, len_cons]; omega

private theorem len_filter_partition (l : List ℕ) (p : ℕ → Bool) :
    len (l.filter p) + len (l.filter fun y => !p y) = len l + 2 := by
  induction l with
  | nil => simp [len_nil]
  | cons a l ih =>
    cases hp : p a <;> simp [hp, len_cons] <;> omega

private theorem insertStep_len (acc : List ℕ) (x : ℕ) :
    len (insertStep acc x) ≤ len acc + (len x + 2) := by
  have hflt : acc.filter (fun y => decide (x < y)) =
      acc.filter (fun y => !decide (y ≤ x)) := by
    congr 1
    funext y
    by_cases hy : y ≤ x
    · have hlt : ¬ x < y := by omega
      simp [hy, hlt]
    · have hlt : x < y := by omega
      simp [hy, hlt]
  have hpart := len_filter_partition acc (fun y => decide (y ≤ x))
  rw [← hflt] at hpart
  have h1 := len_append_nat (acc.filter (· ≤ x) ++ [x]) (acc.filter (x < ·))
  have h2 := len_append_nat (acc.filter (· ≤ x)) [x]
  have hx : len ([x] : List ℕ) = len x + 4 := by simp [len_cons, len_nil]
  unfold insertStep
  omega

@[fun_prop] theorem insertionSort_poly {α : Type} [Enc α] {l : α → List ℕ}
    (hl : PolyT l) : PolyT (fun a => insertionSort (l a)) := by
  obtain ⟨t, ht, _, htl⟩ := len_bound hl
  have hstep : PolyT fun p : α × List ℕ × ℕ => insertStep p.2.1 p.2.2 := by
    unfold insertStep
    fun_prop
  refine Groundwork.PolyT.foldl_add hl (by fun_prop) hstep
    ⟨fun n => t n + 2, ht.add (Groundwork.PB.const 2), fun a acc x hx => ?_⟩
  have hx_le := (len_le_of_mem hx).trans (htl a)
  exact (insertStep_len acc x).trans (Nat.add_le_add_left (Nat.add_le_add_right hx_le 2) (len acc))

private theorem insertStep_perm (acc : List ℕ) (x : ℕ) :
    (insertStep acc x).Perm (x :: acc) := by
  unfold insertStep
  have hp : acc.Perm (acc.filter (· ≤ x) ++ acc.filter (x < ·)) := by
    induction acc with
    | nil => simp
    | cons a l ih =>
      by_cases ha : a ≤ x
      · have hna : ¬ x < a := by omega
        simpa [List.filter_cons, ha, hna] using ih.cons a
      · have hgt : x < a := by omega
        simpa [List.filter_cons, ha, hgt] using List.Perm.trans (ih.cons a) (List.perm_middle.symm)
  rw [List.append_assoc]
  exact List.Perm.trans List.perm_middle (hp.symm.cons x)

private theorem insertStep_pairwise {acc : List ℕ} (hacc : acc.Pairwise (· ≤ ·)) (x : ℕ) :
    (insertStep acc x).Pairwise (· ≤ ·) := by
  have h1 : (acc.filter (· ≤ x)).Pairwise (· ≤ ·) := hacc.filter _
  have h2 : (acc.filter (x < ·)).Pairwise (· ≤ ·) := hacc.filter _
  have hle : ∀ a ∈ acc.filter (· ≤ x), a ≤ x := by
    intro a ha; simp [List.mem_filter] at ha; exact ha.2
  have hgt : ∀ b ∈ acc.filter (x < ·), x ≤ b := by
    intro b hb; simp [List.mem_filter] at hb; omega
  unfold insertStep
  rw [List.append_assoc, List.pairwise_append]
  refine ⟨h1, List.pairwise_cons.mpr ⟨fun b hb => hgt b hb, h2⟩, ?_⟩
  intro a ha b hb
  simp only [List.mem_append, List.mem_singleton] at hb
  rcases hb with rfl | hb
  · exact hle a ha
  · exact le_trans (hle a ha) (hgt b hb)

theorem insertionSort_eq_mergeSort (l : List ℕ) :
    insertionSort l = l.mergeSort := by
  have hfold : ∀ acc, acc.Pairwise (· ≤ ·) →
      (l.foldl insertStep acc).Pairwise (· ≤ ·) ∧ (l.foldl insertStep acc).Perm (l ++ acc) := by
    induction l with
    | nil => intro acc hacc; simp [hacc]
    | cons a l ih =>
      intro acc hacc
      obtain ⟨hpw, hperm⟩ := ih (insertStep acc a) (insertStep_pairwise hacc a)
      refine ⟨hpw, hperm.trans ?_⟩
      exact ((insertStep_perm acc a).append_left l).trans
        (by rw [List.cons_append]; exact List.perm_middle)
  obtain ⟨hpw_ins, hperm_ins⟩ := hfold [] .nil
  simp only [List.append_nil] at hperm_ins
  have hperm_ms : l.mergeSort.Perm l := List.mergeSort_perm l _
  have hpw_ms : l.mergeSort.Pairwise (· ≤ ·) := by
    have h := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc)
      (fun a b => by rcases le_total a b with h | h <;> simp [h]) l
    exact h.imp fun {a b} h => of_decide_eq_true h
  exact (hperm_ins.trans hperm_ms.symm).eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    hpw_ins hpw_ms

def splitStepOk (d x : ℕ) : Bool :=
  decide (2 ≤ d) && decide (d < x) && decide (x % d = 0)

theorem splitStepOk_iff {d x : ℕ} :
    splitStepOk d x = true ↔ 2 ≤ d ∧ d < x ∧ d ∣ x := by
  simp only [splitStepOk, Bool.and_eq_true, decide_eq_true_eq, Nat.dvd_iff_mod_eq_zero, and_assoc]

def splitStepNextWork (ok : Bool) (d x : ℕ) (rest : List ℕ) : List ℕ :=
  bif ok then d :: (x / d) :: rest else rest

def splitStepNextAcc (ok : Bool) (x : ℕ) (acc : List ℕ) : List ℕ :=
  bif ok then acc else x :: acc

def splitStepEmit (work acc : List ℕ) : List Bool :=
  match work with
  | [] => true :: encodeNatListBin (insertionSort acc)
  | y :: _ => false :: pairWord (encState work acc) (countWord y)

@[fun_prop] theorem splitStepOk_poly {α : Type} [Enc α] {d x : α → ℕ}
    (hd : PolyT d) (hx : PolyT x) : PolyT (fun a => splitStepOk (d a) (x a)) := by
  unfold splitStepOk
  fun_prop

@[fun_prop] theorem splitStepNextWork_poly {α : Type} [Enc α]
    {ok : α → Bool} {d x : α → ℕ} {rest : α → List ℕ}
    (hok : PolyT ok) (hd : PolyT d) (hx : PolyT x) (hr : PolyT rest) :
    PolyT (fun a => splitStepNextWork (ok a) (d a) (x a) (rest a)) := by
  unfold splitStepNextWork
  fun_prop

@[fun_prop] theorem splitStepNextAcc_poly {α : Type} [Enc α]
    {ok : α → Bool} {x : α → ℕ} {acc : α → List ℕ}
    (hok : PolyT ok) (hx : PolyT x) (ha : PolyT acc) :
    PolyT (fun a => splitStepNextAcc (ok a) (x a) (acc a)) := by
  unfold splitStepNextAcc
  fun_prop

theorem splitStepEmit_poly {α : Type} [Enc α]
    {work acc : α → List ℕ} (hw : PolyT work) (ha : PolyT acc) :
    PolyT (fun a => splitStepEmit (work a) (acc a)) := by
  refine (Groundwork.PolyT.listCases
    (l := work)
    (d := fun a => true :: encodeNatListBin (insertionSort (acc a)))
    (f := fun a y _ => false :: pairWord (encState (work a) (acc a)) (countWord y))
    hw (by fun_prop) (by fun_prop)).congr fun a => ?_
  cases work a <;> rfl

def splitStepElse (p : (List ℕ × List ℕ) × ℕ) : List Bool :=
  match p.1.1 with
  | [] => true :: encodeNatListBin (insertionSort p.1.2)
  | x :: rest =>
    let ok := splitStepOk p.2 x
    splitStepEmit (splitStepNextWork ok p.2 x rest) (splitStepNextAcc ok x p.1.2)

theorem splitStepElse_poly : PolyT splitStepElse := by
  have hl : PolyT fun p : (List ℕ × List ℕ) × ℕ => p.1.1 := by fun_prop
  have hd : PolyT fun p : (List ℕ × List ℕ) × ℕ =>
      true :: encodeNatListBin (insertionSort p.1.2) := by fun_prop
  have hf : PolyT fun q : ((List ℕ × List ℕ) × ℕ) × ℕ × List ℕ =>
      let ok := splitStepOk q.1.2 q.2.1
      splitStepEmit (splitStepNextWork ok q.1.2 q.2.1 q.2.2)
        (splitStepNextAcc ok q.2.1 q.1.1.2) := by
    have hq_d : PolyT fun q : ((List ℕ × List ℕ) × ℕ) × ℕ × List ℕ => q.1.2 := by fun_prop
    have hq_x : PolyT fun q : ((List ℕ × List ℕ) × ℕ) × ℕ × List ℕ => q.2.1 := by fun_prop
    have hq_r : PolyT fun q : ((List ℕ × List ℕ) × ℕ) × ℕ × List ℕ => q.2.2 := by fun_prop
    have hq_a : PolyT fun q : ((List ℕ × List ℕ) × ℕ) × ℕ × List ℕ => q.1.1.2 := by fun_prop
    have hq_ok := splitStepOk_poly hq_d hq_x
    exact splitStepEmit_poly (splitStepNextWork_poly hq_ok hq_d hq_x hq_r)
      (splitStepNextAcc_poly hq_ok hq_x hq_a)
  refine (Groundwork.PolyT.listCases
    (l := fun p : (List ℕ × List ℕ) × ℕ => p.1.1)
    (d := fun p : (List ℕ × List ℕ) × ℕ => true :: encodeNatListBin (insertionSort p.1.2))
    (f := fun p x rest =>
      let ok := splitStepOk p.2 x
      splitStepEmit (splitStepNextWork ok p.2 x rest) (splitStepNextAcc ok x p.1.2))
    hl hd hf).congr fun p => ?_
  unfold splitStepElse
  cases p.1.1 <;> rfl

def splitStepDecoded (sa : List Bool × List Bool) : List Bool :=
  bif sa.2.isEmpty then
    false :: pairWord (encState [bval sa.1] []) (countWord (bval sa.1))
  else
    splitStepElse (decState sa.1, bval sa.2)

theorem splitStepDecoded_poly : PolyT splitStepDecoded := by
  have h1 : PolyT fun sa : List Bool × List Bool => sa.2.isEmpty := by fun_prop
  have h2 : PolyT fun sa : List Bool × List Bool =>
      false :: pairWord (encState [bval sa.1] []) (countWord (bval sa.1)) := by fun_prop
  have harg : PolyT fun sa : List Bool × List Bool => (decState sa.1, bval sa.2) := by fun_prop
  have h3 : PolyT fun sa : List Bool × List Bool => splitStepElse (decState sa.1, bval sa.2) :=
    Groundwork.PolyT.comp splitStepElse_poly harg
  exact (P2M_Groundwork_PolyT_cond__4c673073da15 h1 h2 h3).congr fun sa => by
    unfold splitStepDecoded
    cases sa.2.isEmpty <;> rfl

def splitStep (inp : List Bool) : List Bool :=
  splitStepDecoded (unpairWord inp)

theorem splitStep_poly : PolyT splitStep := by
  unfold splitStep
  exact Groundwork.PolyT.comp splitStepDecoded_poly (by fun_prop)

/-! ## Section 2: General `RunsWithin` Output-Length Bound and `bitLen`/`countWord` Lemmas -/

private def absCell' (t : Turing.Tape (Option Bool)) (p z : ℤ) : Option Bool :=
  t.nth (z - p)

private theorem nth_mk₁_nil' (k : ℤ) :
    (Turing.Tape.mk₁ ([] : List (Option Bool))).nth k = none := by
  cases k with
  | ofNat n =>
    change (Turing.Tape.mk₁ ([] : List (Option Bool))).nth (n : ℤ) = none
    rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk]
    rfl
  | negSucc n =>
    change (Turing.ListBlank.mk ([] : List (Option Bool))).nth n = none
    rw [Turing.ListBlank.nth_mk]
    rfl

private theorem nth_tape_mk₁_ne_none' {l : List Bool} {z : ℤ}
    (h : (Turing.Tape.mk₁ (l.map some)).nth z ≠ none) :
    0 ≤ z ∧ z.toNat < l.length := by
  cases z with
  | ofNat n =>
    change (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) ≠ none at h
    rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk] at h
    refine ⟨Int.natCast_nonneg n, ?_⟩
    by_contra hge
    have hle : (l.map some).length ≤ n := by simpa using Nat.le_of_not_lt hge
    exact h (List.getI_eq_default (l.map some) hle)
  | negSucc n =>
    exfalso; apply h
    change (Turing.ListBlank.mk ([] : List (Option Bool))).nth n = none
    rw [Turing.ListBlank.nth_mk]; rfl

private theorem nth_tape_mk₁_get' {l : List Bool} {n : ℕ} (hn : n < l.length) :
    (Turing.Tape.mk₁ (l.map some)).nth (n : ℤ) = some l[n] := by
  rw [Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk,
    List.getI_eq_getElem _ (by simpa using hn)]
  simp

private theorem visited_cells_of_step {A : PrimitiveMachine} {input : List Bool}
    {c d : LocatedCfg A} (hw : DetDLP.MachineComposition.LocatedWellFormed c)
    (hvc : ∀ (i : Fin A.tapeCount) (z : ℤ),
      absCell' (c.config.tapes i) (c.position i) z ≠
        absCell' ((locatedInit A input).config.tapes i) 0 z →
      c.lower i ≤ z ∧ z ≤ c.upper i)
    (hs : locatedStep A c = some d) :
    ∀ (i : Fin A.tapeCount) (z : ℤ),
      absCell' (d.config.tapes i) (d.position i) z ≠
        absCell' ((locatedInit A input).config.tapes i) 0 z →
      d.lower i ≤ z ∧ z ≤ d.upper i := by
  unfold locatedStep at hs
  rcases hc : A.step c.config with _ | cfg'
  · simp [hc] at hs
  · have hd : d = c.monitor cfg' := by simpa [hc] using hs.symm
    subst hd
    rcases c with ⟨⟨st, tp⟩, pos, lo, hi⟩
    cases st with
    | inl b => simp [PrimitiveMachine.step] at hc
    | inr q =>
      simp only [PrimitiveMachine.step] at hc
      cases htr : A.transition q (tp (A.scan q)).head with
      | inl b =>
        simp only [htr, Option.some.injEq] at hc
        subst cfg'
        simpa [LocatedCfg.monitor, htr] using hvc
      | inr qa =>
        rcases qa with ⟨q', act⟩
        simp only [htr, Option.some.injEq] at hc
        subst cfg'
        intro i z hne
        simp only [LocatedCfg.monitor, Sum.elim_inr, htr] at hne ⊢
        by_cases hik : i = A.scan q
        · subst i
          have hlo_le : min (lo (A.scan q)) (pos (A.scan q) + headDisplacement act) ≤ lo (A.scan q) :=
            min_le_left _ _
          have hhi_le : hi (A.scan q) ≤ max (hi (A.scan q)) (pos (A.scan q) + headDisplacement act) :=
            le_max_left _ _
          simp only [Function.update_self] at hne ⊢
          cases act with
          | move dir =>
            cases dir <;>
              (simp only [headDisplacement, absCell', Turing.Tape.move_left_nth,
                Turing.Tape.move_right_nth] at hne
               have hne' : absCell' (tp (A.scan q)) (pos (A.scan q)) z ≠
                   absCell' ((locatedInit A input).config.tapes (A.scan q)) 0 z := by
                 simpa [absCell', sub_eq_add_neg, add_assoc] using hne
               have ho := hvc (A.scan q) z hne'
               exact ⟨le_trans hlo_le ho.1, le_trans ho.2 hhi_le⟩)
          | write sym =>
            by_cases hz : z = pos (A.scan q)
            · subst hz
              have hq := hw (A.scan q)
              dsimp only at hq
              exact ⟨le_trans (min_le_left _ _) hq.1, le_trans hq.2 (le_max_left _ _)⟩
            · have hne' : absCell' (tp (A.scan q)) (pos (A.scan q)) z ≠
                  absCell' ((locatedInit A input).config.tapes (A.scan q)) 0 z := by
                have hzn : z - pos (A.scan q) ≠ 0 := sub_ne_zero.mpr hz
                simpa [absCell', headDisplacement, Turing.Tape.write_nth, hzn] using hne
              have ho := hvc (A.scan q) z hne'
              exact ⟨le_trans hlo_le ho.1, le_trans ho.2 hhi_le⟩
        · simp only [Function.update_of_ne hik] at hne ⊢
          exact hvc i z hne

private theorem visited_cells_of_trace {A : PrimitiveMachine} {input : List Bool}
    {k : ℕ} {c : LocatedCfg A}
    (htr : Computation.Trace (locatedStep A) k (locatedInit A input) c) :
    ∀ (i : Fin A.tapeCount) (z : ℤ),
      absCell' (c.config.tapes i) (c.position i) z ≠
        absCell' ((locatedInit A input).config.tapes i) 0 z →
      c.lower i ≤ z ∧ z ≤ c.upper i := by
  let P : LocatedCfg A → Prop := fun d =>
    DetDLP.MachineComposition.LocatedWellFormed d ∧
    ∀ (i : Fin A.tapeCount) (z : ℤ),
      absCell' (d.config.tapes i) (d.position i) z ≠
        absCell' ((locatedInit A input).config.tapes i) 0 z →
      d.lower i ≤ z ∧ z ≤ d.upper i
  have hind : ∀ {m : ℕ} {a b : LocatedCfg A},
      P a → Computation.Trace (locatedStep A) m a b → P b := by
    intro m a b hPa htab
    induction htab with
    | refl => exact hPa
    | @cons m a b' c hs ht ih =>
      exact ih ⟨DetDLP.MachineComposition.locatedWellFormed_step hPa.1 hs,
        visited_cells_of_step hPa.1 hPa.2 hs⟩
  have hP0 : P (locatedInit A input) :=
    ⟨DetDLP.MachineComposition.locatedWellFormed_init A input,
      fun i z h => absurd rfl h⟩
  exact (hind hP0 htr).2

theorem output_length_le_of_runsWithin {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ σ : ℝ}
    (h : RunsWithin A out input output τ σ) :
    output.length ≤ input.length + Nat.ceil σ := by
  obtain ⟨time, final, htr, _, ho, _, hspace⟩ := h
  have hvis : visitedSpace final ≤ Nat.ceil σ := by
    exact_mod_cast le_trans (hspace time final le_rfl htr) (Nat.le_ceil σ)
  have hsingle : (final.upper out - final.lower out + 1).toNat ≤ visitedSpace final :=
    Finset.single_le_sum (f := fun i => (final.upper i - final.lower i + 1).toNat)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ out)
  let p := final.position out
  have hsub : Finset.Ico p (p + (output.length : ℤ)) ⊆
      Finset.Ico (0 : ℤ) (input.length : ℤ) ∪ Finset.Ico (final.lower out) (final.upper out + 1) := by
    intro z hz
    simp only [Finset.mem_Ico] at hz
    have hidx : (z - p).toNat < output.length := by omega
    have hzp : z - p = ((z - p).toNat : ℤ) := by omega
    have hget : absCell' (final.config.tapes out) p z = some output[(z - p).toNat] := by
      have hget' := nth_tape_mk₁_get' hidx
      unfold absCell'
      rw [ho, show (Turing.Tape.mk₁ (output.map some)).nth (z - p) =
        (Turing.Tape.mk₁ (output.map some)).nth ((z - p).toNat : ℤ) from congrArg _ hzp, hget']
    have hne_none : absCell' (final.config.tapes out) p z ≠ none := by rw [hget]; simp
    simp only [Finset.mem_union, Finset.mem_Ico]
    by_cases h0 : absCell' ((locatedInit A input).config.tapes out) 0 z = none
    · right
      have hdiff : absCell' (final.config.tapes out) p z ≠
          absCell' ((locatedInit A input).config.tapes out) 0 z := by
        rw [h0]; exact hne_none
      have hb := visited_cells_of_trace htr out z hdiff
      exact ⟨hb.1, by omega⟩
    · left
      by_cases hout_in : out = A.inputTape
      · have h0' : (Turing.Tape.mk₁ (input.map some)).nth z ≠ none := by
          simpa [absCell', locatedInit, PrimitiveMachine.init, hout_in] using h0
        have hi := nth_tape_mk₁_ne_none' h0'
        exact ⟨hi.1, by omega⟩
      · exfalso; apply h0
        simpa [absCell', locatedInit, PrimitiveMachine.init, hout_in] using nth_mk₁_nil' z
  have hcard := Finset.card_le_card hsub
  have hunion := le_trans hcard (Finset.card_union_le _ _)
  simp only [Int.card_Ico] at hunion
  omega

theorem nat_size_eq_clog {m : ℕ} : m.size = Nat.clog 2 (m + 1) := by
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.size_le]
    have h := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
    omega
  · rw [Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
    have h := Nat.size_le.mp (le_refl m.size)
    omega

theorem bitLen_ge_two {N : ℕ} (hN : 2 ≤ N) : 2 ≤ bitLen (N + 1) := by
  unfold bitLen
  by_contra hlt
  have hle : Nat.clog 2 (N + 1) ≤ 1 := by omega
  have hp := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp hle
  omega

theorem countWord_length_of_pos {y : ℕ} (hy : 1 ≤ y) :
    (countWord y).length = bitLen (y + 1) := by
  have hne : y ≠ 0 := by omega
  unfold countWord bitLen
  rw [if_neg hne, Nat.size_eq_bits_len, nat_size_eq_clog]

theorem countWord_length_eq_log_succ {y : ℕ} (hy : 1 ≤ y) :
    (countWord y).length = Nat.log 2 y + 1 := by
  rw [countWord_length_of_pos hy]
  unfold bitLen
  rw [← nat_size_eq_clog]
  refine Nat.le_antisymm ?_ ?_
  · rw [Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) y
  · have h : Nat.log 2 y < y.size :=
      Nat.lt_size.mpr (Nat.pow_log_le_self 2 (by omega))
    omega

/-! ## Section 3: Splitting Tree Soundness, Measure `dfsRem`, and DFS Loop Invariant -/

private theorem proper_div_quot_bounds {x d : ℕ} (hd2 : 2 ≤ d) (hdx : d < x) (hdvd : d ∣ x) :
    2 ≤ x / d ∧ d * 2 ≤ x ∧ (x / d) * 2 ≤ x := by
  have hmul : d * (x / d) = x := Nat.mul_div_cancel' hdvd
  have hq2 : 2 ≤ x / d := by
    generalize x / d = q at hmul ⊢
    by_contra hlt
    have h01 : q = 0 ∨ q = 1 := by omega
    rcases h01 with h0 | h1 <;> nlinarith
  refine ⟨hq2, ?_, ?_⟩
  · calc d * 2 ≤ d * (x / d) := Nat.mul_le_mul_left d hq2
      _ = x := hmul
  · calc (x / d) * 2 ≤ (x / d) * d := Nat.mul_le_mul_left (x / d) hd2
      _ = x := by rw [mul_comm, hmul]

def splitFun (f : ℕ → ℕ) : ℕ → ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])

def nodeSizeFun (f : ℕ → ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1) (fun _ prev x =>
    let d := f x
    if 2 ≤ d ∧ d < x ∧ d ∣ x then 1 + prev d + prev (x / d) else 1)

private theorem splitFun_succ (f : ℕ → ℕ) (k x : ℕ) :
    splitFun f (k + 1) x =
      if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        splitFun f k (f x) ++ splitFun f k (x / f x)
      else [x] := rfl

private theorem nodeSizeFun_succ (f : ℕ → ℕ) (k x : ℕ) :
    nodeSizeFun f (k + 1) x =
      if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        1 + nodeSizeFun f k (f x) + nodeSizeFun f k (x / f x)
      else 1 := rfl

private theorem splitFun_irrel (f : ℕ → ℕ) :
    ∀ (k₁ k₂ x : ℕ), 2 ≤ x → x < 2 ^ k₁ → x < 2 ^ k₂ → splitFun f k₁ x = splitFun f k₂ x
  | 0, _, x, hx, hlt1, _ => by exfalso; omega
  | k₁ + 1, k₂, x, hx, hlt1, hlt2 => by
    have hk2 : 1 ≤ k₂ := by
      by_contra h0
      have hk0 : k₂ = 0 := by omega
      subst hk0; omega
    obtain ⟨k₂', rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
    rw [splitFun_succ, splitFun_succ]
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, hd_half, hq_half⟩ := proper_div_quot_bounds hd2 hdx hdvd
      have h1d : f x < 2 ^ k₁ := by rw [pow_succ'] at hlt1; omega
      have h2d : f x < 2 ^ k₂' := by rw [pow_succ'] at hlt2; omega
      have h1q : x / f x < 2 ^ k₁ := by rw [pow_succ'] at hlt1; omega
      have h2q : x / f x < 2 ^ k₂' := by rw [pow_succ'] at hlt2; omega
      rw [splitFun_irrel f k₁ k₂' (f x) hd2 h1d h2d,
        splitFun_irrel f k₁ k₂' (x / f x) hq2 h1q h2q]
    · rfl

private theorem nodeSizeFun_irrel (f : ℕ → ℕ) :
    ∀ (k₁ k₂ x : ℕ), 2 ≤ x → x < 2 ^ k₁ → x < 2 ^ k₂ → nodeSizeFun f k₁ x = nodeSizeFun f k₂ x
  | 0, _, x, hx, hlt1, _ => by exfalso; omega
  | k₁ + 1, k₂, x, hx, hlt1, hlt2 => by
    have hk2 : 1 ≤ k₂ := by
      by_contra h0
      have hk0 : k₂ = 0 := by omega
      subst hk0; omega
    obtain ⟨k₂', rfl⟩ : ∃ k₂', k₂ = k₂' + 1 := ⟨k₂ - 1, by omega⟩
    rw [nodeSizeFun_succ, nodeSizeFun_succ]
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, hd_half, hq_half⟩ := proper_div_quot_bounds hd2 hdx hdvd
      have h1d : f x < 2 ^ k₁ := by rw [pow_succ'] at hlt1; omega
      have h2d : f x < 2 ^ k₂' := by rw [pow_succ'] at hlt2; omega
      have h1q : x / f x < 2 ^ k₁ := by rw [pow_succ'] at hlt1; omega
      have h2q : x / f x < 2 ^ k₂' := by rw [pow_succ'] at hlt2; omega
      rw [nodeSizeFun_irrel f k₁ k₂' (f x) hd2 h1d h2d,
        nodeSizeFun_irrel f k₁ k₂' (x / f x) hq2 h1q h2q]
    · rfl

def canonSplit (f : ℕ → ℕ) (x : ℕ) : List ℕ := splitFun f x x
def treeNodes (f : ℕ → ℕ) (x : ℕ) : ℕ := nodeSizeFun f x x

private theorem splitFun_eq_canonSplit {f : ℕ → ℕ} {k x : ℕ} (hx : 2 ≤ x) (hlt : x < 2 ^ k) :
    splitFun f k x = canonSplit f x :=
  splitFun_irrel f k x x hx hlt Nat.lt_two_pow_self

private theorem nodeSizeFun_eq_treeNodes {f : ℕ → ℕ} {k x : ℕ} (hx : 2 ≤ x) (hlt : x < 2 ^ k) :
    nodeSizeFun f k x = treeNodes f x :=
  nodeSizeFun_irrel f k x x hx hlt Nat.lt_two_pow_self

private theorem canonSplit_eq {f : ℕ → ℕ} {x : ℕ} (hx : 2 ≤ x) :
    canonSplit f x =
      if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        canonSplit f (f x) ++ canonSplit f (x / f x)
      else [x] := by
  have hx1 : x < 2 ^ (x + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by decide) (by omega))
  rw [← splitFun_eq_canonSplit hx hx1, splitFun_succ]
  split_ifs with h
  · rcases h with ⟨hd2, hdx, hdvd⟩
    obtain ⟨hq2, _, _⟩ := proper_div_quot_bounds hd2 hdx hdvd
    have hlt_x : x < 2 ^ x := Nat.lt_two_pow_self
    rw [splitFun_eq_canonSplit hd2 (lt_trans hdx hlt_x),
      splitFun_eq_canonSplit hq2 (lt_of_le_of_lt (Nat.div_le_self _ _) hlt_x)]
  · rfl

private theorem treeNodes_eq {f : ℕ → ℕ} {x : ℕ} (hx : 2 ≤ x) :
    treeNodes f x =
      if 2 ≤ f x ∧ f x < x ∧ f x ∣ x then
        1 + treeNodes f (f x) + treeNodes f (x / f x)
      else 1 := by
  have hx1 : x < 2 ^ (x + 1) := lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by decide) (by omega))
  rw [← nodeSizeFun_eq_treeNodes hx hx1, nodeSizeFun_succ]
  split_ifs with h
  · rcases h with ⟨hd2, hdx, hdvd⟩
    obtain ⟨hq2, _, _⟩ := proper_div_quot_bounds hd2 hdx hdvd
    have hlt_x : x < 2 ^ x := Nat.lt_two_pow_self
    rw [nodeSizeFun_eq_treeNodes hd2 (lt_trans hdx hlt_x),
      nodeSizeFun_eq_treeNodes hq2 (lt_of_le_of_lt (Nat.div_le_self _ _) hlt_x)]
  · rfl

private theorem treeNodes_pos (f : ℕ → ℕ) (x : ℕ) : 1 ≤ treeNodes f x := by
  by_cases hx : 2 ≤ x
  · rw [treeNodes_eq hx]
    split_ifs <;> omega
  · unfold treeNodes
    cases x with
    | zero => simp [nodeSizeFun]
    | succ m =>
      have hm : m = 0 := by omega
      subst hm
      simp [nodeSizeFun]; split_ifs <;> omega

private theorem treeNodes_add_one (f : ℕ → ℕ) :
    ∀ x : ℕ, 2 ≤ x → treeNodes f x + 1 = 2 * (canonSplit f x).length
  | x, hx => by
    rw [treeNodes_eq hx, canonSplit_eq hx]
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, hd_half, hq_half⟩ := proper_div_quot_bounds hd2 hdx hdvd
      have ih1 := treeNodes_add_one f (f x) hd2
      have ih2 := treeNodes_add_one f (x / f x) hq2
      rw [List.length_append]
      omega
    · simp
decreasing_by
  all_goals omega

private theorem canonSplit_prod_ge2 (f : ℕ → ℕ) :
    ∀ x : ℕ, 2 ≤ x → (canonSplit f x).prod = x ∧ ∀ p ∈ canonSplit f x, 2 ≤ p
  | x, hx => by
    rw [canonSplit_eq hx]
    split_ifs with h
    · rcases h with ⟨hd2, hdx, hdvd⟩
      obtain ⟨hq2, _, _⟩ := proper_div_quot_bounds hd2 hdx hdvd
      have ih1 := canonSplit_prod_ge2 f (f x) hd2
      have ih2 := canonSplit_prod_ge2 f (x / f x) hq2
      refine ⟨?_, ?_⟩
      · rw [List.prod_append, ih1.1, ih2.1, Nat.mul_div_cancel' hdvd]
      · intro p hp
        rw [List.mem_append] at hp
        rcases hp with hp | hp
        · exact ih1.2 p hp
        · exact ih2.2 p hp
    · exact ⟨by simp, fun p hp => by simp at hp; omega⟩
decreasing_by
  all_goals omega

private theorem list_prod_bounds {L : List ℕ} (hge : ∀ y ∈ L, 2 ≤ y) :
    2 ^ (L.map (Nat.log 2)).sum ≤ L.prod ∧
    L.length ≤ (L.map (Nat.log 2)).sum ∧
    (L.map (fun y => (countWord y).length)).sum = (L.map (Nat.log 2)).sum + L.length ∧
    ∀ y ∈ L, y ≤ L.prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : 2 ≤ a := hge a (by simp)
    have ht := ih (fun y hy => hge y (by simp [hy]))
    have hlog_ge1 : 1 ≤ Nat.log 2 a := Nat.log_pos (by decide) ha
    have hpow_le : 2 ^ Nat.log 2 a ≤ a := Nat.pow_log_le_self 2 (by omega)
    have hcw : (countWord a).length = Nat.log 2 a + 1 := countWord_length_eq_log_succ (by omega)
    have htprod_ge1 : 1 ≤ t.prod := Nat.one_le_pow _ 2 (by decide) |>.trans ht.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
      exact Nat.mul_le_mul hpow_le ht.1
    · simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    · simp only [List.map_cons, List.sum_cons, List.length_cons, hcw, ht.2.2.1]
      omega
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp only [List.prod_cons]
        exact Nat.le_mul_of_pos_right y (by omega)
      · have hy_t := ht.2.2.2 y hy
        simp only [List.prod_cons]
        exact le_trans hy_t (Nat.le_mul_of_pos_left t.prod (by omega))

private theorem list_len_bounds_of_prod {L : List ℕ} {N : ℕ} (_hN : 2 ≤ N)
    (hge : ∀ y ∈ L, 2 ≤ y) (hprod : L.prod = N) :
    let n := bitLen (N + 1)
    L.length ≤ n ∧
    (L.map (fun y => (countWord y).length)).sum ≤ 2 * n ∧
    (∀ y ∈ L, y ≤ N) := by
  intro n
  obtain ⟨hb_pow, hb_len, hb_sum, hb_mem⟩ := list_prod_bounds hge
  have hN_lt : N < 2 ^ n := by
    have h1 : N + 1 ≤ 2 ^ n := Nat.le_pow_clog (by decide : 1 < 2) (N + 1)
    omega
  have hsum_lt : (L.map (Nat.log 2)).sum < n := by
    rw [← Nat.pow_lt_pow_iff_right (by decide : 1 < 2)]
    exact lt_of_le_of_lt (hb_pow.trans (by rw [hprod])) hN_lt
  refine ⟨by omega, by omega, fun y hy => by rw [← hprod]; exact hb_mem y hy⟩

/-! ## Section 4: Calculus-Free Log/Sqrt Real Analysis Helpers & Main Complexity Reduction -/

private theorem one_le_logSafe (x : ℝ) : 1 ≤ logSafe x := le_max_left _ _
private theorem logSafe_pos (x : ℝ) : 0 < logSafe x := lt_of_lt_of_le zero_lt_one (one_le_logSafe x)

private theorem logSafe_eq_log_div {x : ℝ} (hx : 2 ≤ x) :
    logSafe x = Real.log x / Real.log 2 := by
  have h1 : 1 ≤ Real.logb 2 x := by
    rw [← Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx
  unfold logSafe
  rw [max_eq_right hx, max_eq_right h1, Real.logb]

theorem div_sqrt_logSafe_mono {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    a / Real.sqrt (logSafe a) ≤ b / Real.sqrt (logSafe b) := by
  have hb : 2 ≤ b := le_trans ha hab
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hLa_pos : 0 < logSafe a := logSafe_pos a
  have hLb_pos : 0 < logSafe b := logSafe_pos b
  have hsa_pos : 0 < Real.sqrt (logSafe a) := Real.sqrt_pos.mpr hLa_pos
  have hsb_pos : 0 < Real.sqrt (logSafe b) := Real.sqrt_pos.mpr hLb_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hloga_gt : (1 : ℝ) / 2 < Real.log a :=
    lt_of_lt_of_le hlog2_gt (Real.log_le_log (by norm_num) ha)
  have hba_ge1 : 1 ≤ b / a := (one_le_div ha_pos).mpr hab
  have hlog_step : Real.log b - Real.log a ≤ (b / a - 1) * ((b / a + 1) * Real.log a) := by
    calc Real.log b - Real.log a
        = Real.log (b / a) := (Real.log_div hb_pos.ne' ha_pos.ne').symm
      _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb_pos ha_pos)
      _ = (b / a - 1) * 1 := (mul_one _).symm
      _ ≤ (b / a - 1) * ((b / a + 1) * Real.log a) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have hmul_sq : a ^ 2 * (Real.log b - Real.log a) ≤ (b ^ 2 - a ^ 2) * Real.log a := by
    calc a ^ 2 * (Real.log b - Real.log a)
        ≤ a ^ 2 * ((b / a - 1) * ((b / a + 1) * Real.log a)) :=
          mul_le_mul_of_nonneg_left hlog_step (sq_nonneg a)
      _ = (b ^ 2 - a ^ 2) * Real.log a := by field_simp [ha_pos.ne']; ring
  have hlog_sq : a ^ 2 * Real.log b ≤ b ^ 2 * Real.log a := by linarith
  have hlogSafe_sq : a ^ 2 * logSafe b ≤ b ^ 2 * logSafe a := by
    rw [logSafe_eq_log_div ha, logSafe_eq_log_div hb]
    calc a ^ 2 * (Real.log b / Real.log 2)
        = (a ^ 2 * Real.log b) / Real.log 2 := by ring
      _ ≤ (b ^ 2 * Real.log a) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog_sq hlog2_pos.le
      _ = b ^ 2 * (Real.log a / Real.log 2) := by ring
  have hsqrt_sq := Real.sqrt_le_sqrt hlogSafe_sq
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_mul (sq_nonneg b),
    Real.sqrt_sq ha_pos.le, Real.sqrt_sq hb_pos.le] at hsqrt_sq
  exact (div_le_div_iff₀ hsa_pos hsb_pos).mpr hsqrt_sq

private theorem one_le_n_div_sqrt_logSafe {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ (n : ℝ) / Real.sqrt (logSafe (n : ℝ)) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogn : Real.log (n : ℝ) ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hn_pos
    linarith
  have hL_le : logSafe (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [logSafe_eq_log_div hn2, div_le_iff₀ (by linarith)]
    have h2n : (2 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have h12 : (n : ℝ) ^ 2 * ((1 : ℝ) / 2) ≤ (n : ℝ) ^ 2 * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2_gt.le (sq_nonneg _)
    linarith
  have hsqrt_le : Real.sqrt (logSafe (n : ℝ)) ≤ (n : ℝ) := by
    calc Real.sqrt (logSafe (n : ℝ))
        ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hL_le
      _ = (n : ℝ) := Real.sqrt_sq hn_pos.le
  exact (one_le_div (Real.sqrt_pos.mpr (logSafe_pos _))).mpr hsqrt_le

private theorem np1_le_exp_sqrt_logSafe {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) + 1 ≤ (2 : ℝ) ^ ((48 : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  set L : ℝ := logSafe (n : ℝ)
  have hL1 : 1 ≤ L := one_le_logSafe _
  have hL_pos : 0 < L := logSafe_pos _
  have hnp1_pow : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (L + 1) := by
    have hn_eq : (n : ℝ) = (2 : ℝ) ^ Real.logb 2 (n : ℝ) :=
      (Real.rpow_logb (by norm_num) (by norm_num) hn_pos).symm
    have hlogb_le_L : Real.logb 2 (n : ℝ) ≤ L := by
      have : max (2 : ℝ) (n : ℝ) = (n : ℝ) := max_eq_right hn2
      dsimp only [L]; unfold logSafe; rw [this]; exact le_max_right _ _
    calc (n : ℝ) + 1
        ≤ 2 * (n : ℝ) := by linarith
      _ = 2 * (2 : ℝ) ^ Real.logb 2 (n : ℝ) := by rw [← hn_eq]
      _ ≤ 2 * (2 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlogb_le_L) (by norm_num)
      _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ L := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (1 + L) := (Real.rpow_add (by norm_num) 1 L).symm
      _ = (2 : ℝ) ^ (L + 1) := by ring_nf
  have hlog2_gt : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL_le : L ≤ 8 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
    have hq := Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ ((1 : ℝ) / 4))
    rw [Real.log_rpow hn_pos] at hq
    have hlog_le : Real.log (n : ℝ) ≤ 4 * (n : ℝ) ^ ((1 : ℝ) / 4) := by linarith
    dsimp only [L]
    rw [logSafe_eq_log_div hn2, div_le_iff₀ (by linarith)]
    have hm : (8 * (n : ℝ) ^ ((1 : ℝ) / 4)) * (1 / 2) ≤ (8 * (n : ℝ) ^ ((1 : ℝ) / 4)) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2_gt.le (by positivity)
    linarith
  have hL3 : L ^ 3 ≤ (24 * (n : ℝ)) ^ 2 := by
    have hp1 : L ^ 3 ≤ (8 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 :=
      pow_le_pow_left₀ hL_pos.le hL_le 3
    have hn34 : ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 ≤ (n : ℝ) ^ 2 := by
      calc ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3
          = ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ ((3 : ℕ) : ℝ) := (Real.rpow_natCast _ 3).symm
        _ = (n : ℝ) ^ (((1 : ℝ) / 4) * (3 : ℝ)) := by rw [← Real.rpow_mul hn_pos.le]; norm_num
        _ ≤ (n : ℝ) ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
        _ = (n : ℝ) ^ 2 := Real.rpow_natCast _ 2
    have h512 : (8 * (n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 = 512 * ((n : ℝ) ^ ((1 : ℝ) / 4)) ^ 3 := by ring
    have hn_sq_nn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have hsq_eq : (L * Real.sqrt L) ^ 2 = L ^ 3 := by
    calc (L * Real.sqrt L) ^ 2 = L ^ 2 * (Real.sqrt L) ^ 2 := by ring
      _ = L ^ 2 * L := by rw [Real.sq_sqrt hL_pos.le]
      _ = L ^ 3 := by ring
  have hLsqrt : L * Real.sqrt L ≤ 24 * (n : ℝ) := by
    have hs := Real.sqrt_le_sqrt (hsq_eq ▸ hL3)
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hs
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
  have hexp : L + 1 ≤ (48 : ℝ) * (n : ℝ) / Real.sqrt L := by
    rw [le_div_iff₀ hsqrt_pos]
    calc (L + 1) * Real.sqrt L ≤ (2 * L) * Real.sqrt L :=
          mul_le_mul_of_nonneg_right (by linarith) hsqrt_pos.le
      _ = 2 * (L * Real.sqrt L) := by ring
      _ ≤ 2 * (24 * (n : ℝ)) := by linarith
      _ = 48 * (n : ℝ) := by ring
  exact le_trans hnp1_pow (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)

private theorem driver_space_arith (Kd K_loop n K_sp : ℕ) (hKl : 1 ≤ K_loop)
    (hK1 : K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) + 1 ≤ K_sp)
    (hK2 : K_loop * max Kd 1 ≤ K_sp) :
    let maxLen := 40 * n + Nat.ceil (polyBound Kd n) + 20
    polyBound K_loop maxLen + (K_loop : ℝ) * (polyBound Kd n + 1) ≤ polyBound K_sp n := by
  intro maxLen
  let x : ℝ := (n : ℝ) + 1
  let D : ℕ := max Kd 1
  have hx1 : 1 ≤ x := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; dsimp [x]; linarith
  have hD1 : 1 ≤ D := le_max_right Kd 1
  have hDKd : Kd ≤ D := le_max_left Kd 1
  have hxD0 : 1 ≤ x ^ D := one_le_pow₀ hx1
  have hxD1 : x ≤ x ^ D := by
    calc x = x ^ 1 := (pow_one _).symm
      _ ≤ x ^ D := pow_le_pow_right₀ hx1 hD1
  have hxDKd : x ^ Kd ≤ x ^ D := pow_le_pow_right₀ hx1 hDKd
  have hxD_nn : 0 ≤ x ^ D := by positivity
  have hpb_nn : 0 ≤ polyBound Kd n := by unfold polyBound; positivity
  have hceil : (Nat.ceil (polyBound Kd n) : ℝ) < polyBound Kd n + 1 := Nat.ceil_lt_add_one hpb_nn
  have hmax_cast : (maxLen : ℝ) + 1 = 40 * (n : ℝ) + (Nat.ceil (polyBound Kd n) : ℝ) + 21 := by
    dsimp [maxLen]; push_cast; ring
  have hpb_bound : polyBound Kd n ≤ (Kd : ℝ) * x ^ D := by
    unfold polyBound
    exact mul_le_mul_of_nonneg_left hxDKd (Nat.cast_nonneg _)
  have hmax_le : (maxLen : ℝ) + 1 ≤ ((Kd + 63 : ℕ) : ℝ) * x ^ D := by
    have h40 : 40 * (n : ℝ) ≤ 40 * x ^ D := by linarith
    have h22 : (22 : ℝ) ≤ 22 * x ^ D := by linarith
    have hsum : (maxLen : ℝ) + 1 ≤ (Kd : ℝ) * x ^ D + 63 * x ^ D := by linarith
    calc (maxLen : ℝ) + 1
        ≤ (Kd : ℝ) * x ^ D + 63 * x ^ D := hsum
      _ = ((Kd + 63 : ℕ) : ℝ) * x ^ D := by push_cast; ring
  have hpow_max : ((maxLen : ℝ) + 1) ^ K_loop ≤ ((Kd + 63 : ℕ) : ℝ) ^ K_loop * x ^ (K_loop * D) := by
    calc ((maxLen : ℝ) + 1) ^ K_loop
        ≤ (((Kd + 63 : ℕ) : ℝ) * x ^ D) ^ K_loop := pow_le_pow_left₀ (by positivity) hmax_le K_loop
      _ = ((Kd + 63 : ℕ) : ℝ) ^ K_loop * (x ^ D) ^ K_loop := mul_pow _ _ _
      _ = ((Kd + 63 : ℕ) : ℝ) ^ K_loop * x ^ (K_loop * D) := by rw [← pow_mul, mul_comm D K_loop]
  have hxKD : x ^ (K_loop * D) ≤ x ^ K_sp := pow_le_pow_right₀ hx1 hK2
  have hxD_sp : x ^ D ≤ x ^ K_sp := pow_le_pow_right₀ hx1 (le_trans (Nat.le_mul_of_pos_left D (by omega)) hK2)
  have h1 : polyBound K_loop maxLen ≤ ((K_loop * (Kd + 63) ^ K_loop : ℕ) : ℝ) * x ^ K_sp := by
    unfold polyBound
    calc (K_loop : ℝ) * ((maxLen : ℝ) + 1) ^ K_loop
        ≤ (K_loop : ℝ) * (((Kd + 63 : ℕ) : ℝ) ^ K_loop * x ^ (K_loop * D)) :=
          mul_le_mul_of_nonneg_left hpow_max (Nat.cast_nonneg _)
      _ = ((K_loop * (Kd + 63) ^ K_loop : ℕ) : ℝ) * x ^ (K_loop * D) := by push_cast; ring
      _ ≤ ((K_loop * (Kd + 63) ^ K_loop : ℕ) : ℝ) * x ^ K_sp :=
          mul_le_mul_of_nonneg_left hxKD (by positivity)
  have h2 : (K_loop : ℝ) * (polyBound Kd n + 1) ≤ ((K_loop * (Kd + 1) : ℕ) : ℝ) * x ^ K_sp := by
    have hp1 : polyBound Kd n + 1 ≤ ((Kd + 1 : ℕ) : ℝ) * x ^ D := by
      have hsum : (Kd : ℝ) * x ^ D + 1 ≤ ((Kd + 1 : ℕ) : ℝ) * x ^ D := by
        push_cast; linarith
      linarith
    calc (K_loop : ℝ) * (polyBound Kd n + 1)
        ≤ (K_loop : ℝ) * (((Kd + 1 : ℕ) : ℝ) * x ^ D) := mul_le_mul_of_nonneg_left hp1 (Nat.cast_nonneg _)
      _ = ((K_loop * (Kd + 1) : ℕ) : ℝ) * x ^ D := by push_cast; ring
      _ ≤ ((K_loop * (Kd + 1) : ℕ) : ℝ) * x ^ K_sp := mul_le_mul_of_nonneg_left hxD_sp (by positivity)
  have hcoeff : ((K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) : ℕ) : ℝ) ≤ (K_sp : ℝ) := by
    exact_mod_cast (by omega : K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) ≤ K_sp)
  calc polyBound K_loop maxLen + (K_loop : ℝ) * (polyBound Kd n + 1)
      ≤ ((K_loop * (Kd + 63) ^ K_loop : ℕ) : ℝ) * x ^ K_sp +
          ((K_loop * (Kd + 1) : ℕ) : ℝ) * x ^ K_sp := by linarith
    _ = ((K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) : ℕ) : ℝ) * x ^ K_sp := by
        push_cast; ring
    _ ≤ (K_sp : ℝ) * x ^ K_sp := mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = polyBound K_sp n := by simp [polyBound, x]

private theorem driver_time_arith (Kd K_loop K_sp K_tm n rounds : ℕ) (hKl : 1 ≤ K_loop)
    (hrounds : rounds ≤ 2 * n) (hn : 2 ≤ n)
    (hK1 : K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) + 1 ≤ K_sp)
    (hK2 : K_loop * max Kd 1 ≤ K_sp)
    (hKtm : K_tm = 2 * K_sp + 2 * K_loop + 48 * (K_sp + 1) + Kd) :
    let maxLen := 40 * n + Nat.ceil (polyBound Kd n) + 20
    let τO := (2 : ℝ) ^ ((Kd : ℝ) * n / Real.sqrt (logSafe n))
    let σO := polyBound Kd n
    (rounds : ℝ) * (polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1)) ≤
      (2 : ℝ) ^ ((K_tm : ℝ) * n / Real.sqrt (logSafe n)) := by
  intro maxLen τO σO
  have hspace := driver_space_arith Kd K_loop n K_sp hKl hK1 hK2
  dsimp only at hspace
  have hτ_nn : 0 ≤ (Kd : ℝ) * n / Real.sqrt (logSafe n) := by
    exact div_nonneg (by positivity) (Real.sqrt_nonneg _)
  have h1_le_τO : 1 ≤ τO := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hτ_nn
  have h1_le_xp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ K_sp := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hinner : polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1) ≤
      ((K_sp + K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO := by
    have hsplit : polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1) =
        (polyBound K_loop maxLen + (K_loop : ℝ) * (σO + 1)) + (K_loop : ℝ) * τO := by ring
    rw [hsplit]
    have ha : polyBound K_loop maxLen + (K_loop : ℝ) * (σO + 1) ≤ (K_sp : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO := by
      calc polyBound K_loop maxLen + (K_loop : ℝ) * (σO + 1)
          ≤ polyBound K_sp n := hspace
        _ = (K_sp : ℝ) * ((n : ℝ) + 1) ^ K_sp * 1 := by simp [polyBound]
        _ ≤ (K_sp : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO :=
            mul_le_mul_of_nonneg_left h1_le_τO (by positivity)
    have hb : (K_loop : ℝ) * τO ≤ (K_loop : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO := by
      calc (K_loop : ℝ) * τO
          = (K_loop : ℝ) * 1 * τO := by ring
        _ ≤ (K_loop : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1_le_xp (Nat.cast_nonneg _))
              (by positivity)
    calc (polyBound K_loop maxLen + (K_loop : ℝ) * (σO + 1)) + (K_loop : ℝ) * τO
        ≤ (K_sp : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO + (K_loop : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO := by
          linarith
      _ = ((K_sp + K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO := by push_cast; ring
  have hrounds_le : (rounds : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hr : (rounds : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hrounds
    linarith
  have htot : (rounds : ℝ) * (polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1)) ≤
      ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K_sp + 1) * τO := by
    calc (rounds : ℝ) * (polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1))
        ≤ (2 * ((n : ℝ) + 1)) * (((K_sp + K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ K_sp * τO) :=
          mul_le_mul hrounds_le hinner (by dsimp only [τO, σO]; unfold polyBound; positivity) (by positivity)
      _ = ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K_sp + 1) * τO := by
          rw [pow_succ]; push_cast; ring
  let q : ℝ := (n : ℝ) / Real.sqrt (logSafe (n : ℝ))
  have hq1 : 1 ≤ q := one_le_n_div_sqrt_logSafe hn
  have hC : ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * q) := by
    have hlt : 2 * K_sp + 2 * K_loop ≤ 2 ^ (2 * K_sp + 2 * K_loop) := le_of_lt Nat.lt_two_pow_self
    have hltR : ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast hlt
    refine le_trans hltR (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_)
    calc ((2 * K_sp + 2 * K_loop : ℕ) : ℝ)
        = ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * 1 := (mul_one _).symm
      _ ≤ ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * q :=
          mul_le_mul_of_nonneg_left hq1 (Nat.cast_nonneg _)
  have hpow_np1 : ((n : ℝ) + 1) ^ (K_sp + 1) ≤
      (2 : ℝ) ^ (((48 * (K_sp + 1) : ℕ) : ℝ) * q) := by
    have hbase := np1_le_exp_sqrt_logSafe hn
    calc ((n : ℝ) + 1) ^ (K_sp + 1)
        ≤ ((2 : ℝ) ^ ((48 : ℝ) * q)) ^ (K_sp + 1) := by
          have : (48 : ℝ) * q = (48 : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)) := by ring
          rw [this]
          exact pow_le_pow_left₀ (by positivity) hbase (K_sp + 1)
      _ = ((2 : ℝ) ^ ((48 : ℝ) * q)) ^ ((K_sp + 1 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (2 : ℝ) ^ (((48 : ℝ) * q) * ((K_sp + 1 : ℕ) : ℝ)) := by rw [← Real.rpow_mul (by norm_num)]
      _ = (2 : ℝ) ^ (((48 * (K_sp + 1) : ℕ) : ℝ) * q) := by congr 1; push_cast; ring
  calc (rounds : ℝ) * (polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1))
      ≤ ((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (K_sp + 1) * τO := htot
    _ ≤ (2 : ℝ) ^ (((2 * K_sp + 2 * K_loop : ℕ) : ℝ) * q) *
          (2 : ℝ) ^ (((48 * (K_sp + 1) : ℕ) : ℝ) * q) *
          (2 : ℝ) ^ ((Kd : ℝ) * q) := by
        have hτ_eq : τO = (2 : ℝ) ^ ((Kd : ℝ) * q) := by
          dsimp [τO, q]; ring_nf
        rw [← hτ_eq]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC hpow_np1 (by positivity) (by positivity))
          (by positivity)
    _ = (2 : ℝ) ^ ((K_tm : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        rw [hKtm]
        dsimp [q]
        push_cast
        ring

end DetDLP.FactorSplittingDriver

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP.FactorSplittingDriver

theorem factor_splitting_driver_machine_proved
    (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ)
    (hd : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N + 1)
      RunsWithin Md od (countWord N) (countWord (f N))
        ((2 : ℝ) ^ ((Kd : ℝ) * n / Real.sqrt (logSafe n))) (polyBound Kd n)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x / d) else [x])
        RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n) := by
  obtain ⟨M, out, K_loop, hK_loop1, hloop⟩ := m89_polyT_oracle_loop splitStep splitStep_poly Md od
  let K_sp := K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) + K_loop * max Kd 1 + 1
  let K_tm := 2 * K_sp + 2 * K_loop + 48 * (K_sp + 1) + Kd
  let K := max K_sp K_tm
  refine ⟨M, out, K, fun N hN => ?_⟩
  dsimp only
  set n := bitLen (N + 1)
  have hn2 : 2 ≤ n := bitLen_ge_two hN
  have hN_lt : N < 2 ^ n := by
    have h1 : N + 1 ≤ 2 ^ n := Nat.le_pow_clog (by decide : 1 < 2) (N + 1)
    omega
  have hsplit_canon : splitFun f n N = canonSplit f N := splitFun_eq_canonSplit hN hN_lt
  change RunsWithin M out (countWord N) (encodeNatListBin ((splitFun f n N).mergeSort))
    ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n)
  rw [hsplit_canon]
  let τO : ℝ := (2 : ℝ) ^ ((Kd : ℝ) * n / Real.sqrt (logSafe n))
  let σO : ℝ := polyBound Kd n
  let maxLen : ℕ := 40 * n + Nat.ceil σO + 20
  have hτO_nn : 0 ≤ τO := by positivity
  have hσO_nn : 0 ≤ σO := by unfold σO polyBound; positivity
  have hloop_inst := hloop τO σO hτO_nn hσO_nn
  dsimp only at hloop_inst
  change ∀ (rounds maxL : ℕ) (input output : List Bool), 1 ≤ rounds → _ →
    RunsWithin M out input output
      ((rounds : ℝ) * (polyBound K_loop maxL + (K_loop : ℝ) * (τO + σO + 1)))
      (polyBound K_loop maxL + (K_loop : ℝ) * (σO + 1)) at hloop_inst
  let loopRuns : ℕ → List Bool → List Bool → List Bool → ℕ → Prop :=
    Nat.rec (motive := fun _ => List Bool → List Bool → List Bool → ℕ → Prop)
      (fun _ _ _ _ => False)
      (fun _ prev st ans outW maxL =>
        (splitStep (pairWord st ans) = true :: outW ∧
          (pairWord st ans).length ≤ maxL ∧ outW.length ≤ maxL) ∨
        (∃ st' q ans',
          splitStep (pairWord st ans) = false :: pairWord st' q ∧
          (pairWord st ans).length ≤ maxL ∧
          (pairWord st' q).length ≤ maxL ∧
          ans'.length ≤ maxL ∧
          RunsWithin Md od q ans' τO σO ∧
          prev st' ans' outW maxL))
  have horacle : ∀ y : ℕ, 2 ≤ y → y ≤ N →
      RunsWithin Md od (countWord y) (countWord (f y)) τO σO ∧
      (countWord y).length ≤ n ∧
      (countWord (f y)).length ≤ n + Nat.ceil σO := by
    intro y hy2 hyN
    let m := bitLen (y + 1)
    have hm2 : 2 ≤ m := bitLen_ge_two hy2
    have hmn : m ≤ n := Nat.clog_mono_right 2 (by omega)
    have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
    have hdiv : (m : ℝ) / Real.sqrt (logSafe (m : ℝ)) ≤ (n : ℝ) / Real.sqrt (logSafe (n : ℝ)) :=
      div_sqrt_logSafe_mono hm2R hmnR
    have hτm : (2 : ℝ) ^ ((Kd : ℝ) * m / Real.sqrt (logSafe m)) ≤ τO := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      calc (Kd : ℝ) * m / Real.sqrt (logSafe m)
          = (Kd : ℝ) * ((m : ℝ) / Real.sqrt (logSafe m)) := by ring
        _ ≤ (Kd : ℝ) * ((n : ℝ) / Real.sqrt (logSafe n)) :=
            mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
        _ = (Kd : ℝ) * n / Real.sqrt (logSafe n) := by ring
    have hσm : polyBound Kd m ≤ σO := by
      unfold σO polyBound
      have h1 : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 Kd) (Nat.cast_nonneg _)
    have hrun_y := DetDLP.MachineComposition.runsWithin_mono (hd y hy2) hτm hσm
    have hqlen : (countWord y).length ≤ n := by
      rw [countWord_length_of_pos (by omega)]
      exact hmn
    have halen : (countWord (f y)).length ≤ n + Nat.ceil σO := by
      have h1 := output_length_le_of_runsWithin hrun_y
      omega
    exact ⟨hrun_y, hqlen, halen⟩
  let outW := encodeNatListBin ((canonSplit f N).mergeSort)
  have houtW_len : outW.length ≤ maxLen := by
    have hc := canonSplit_prod_ge2 f N hN
    have hb := list_len_bounds_of_prod hN hc.2 hc.1
    have hperm : ((canonSplit f N).mergeSort).Perm (canonSplit f N) :=
      List.mergeSort_perm _ _
    have hsum_eq : (((canonSplit f N).mergeSort).map (fun a => (countWord a).length)).sum =
        ((canonSplit f N).map (fun a => (countWord a).length)).sum :=
      (hperm.map _).sum_eq
    have hlen_eq : ((canonSplit f N).mergeSort).length = (canonSplit f N).length := hperm.length_eq
    dsimp only [outW, maxLen]
    rw [encodeNatListBin_length, hsum_eq, hlen_eq]
    omega
  have hdfs : ∀ (rem : ℕ), 1 ≤ rem →
      ∀ (work acc : List ℕ) (x : ℕ) (rest : List ℕ),
        work = x :: rest →
        rem = (work.map (treeNodes f)).sum →
        (∀ y ∈ work, 2 ≤ y) →
        (∀ y ∈ acc, 2 ≤ y) →
        (work ++ acc).prod = N →
        acc.reverse ++ work.flatMap (canonSplit f) = canonSplit f N →
        loopRuns rem (encState work acc) (countWord (f x)) outW maxLen := by
    intro rem
    induction rem using Nat.strong_induction_on with
    | h rem ih =>
      intro hrem work acc x rest hwork hrem_eq hge_w hge_a hprod hinv
      have hlen_bounds :
          (encState work acc).length ≤ 18 * n + 4 ∧
          (∀ y ∈ work, y ≤ N) := by
        have hgeL : ∀ y ∈ work ++ acc, 2 ≤ y := by
          intro y hy
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hge_w y hy
          · exact hge_a y hy
        have hbL := list_len_bounds_of_prod hN hgeL hprod
        have hsum_split : ((work ++ acc).map (fun a => (countWord a).length)).sum =
            (work.map (fun a => (countWord a).length)).sum +
            (acc.map (fun a => (countWord a).length)).sum := by
          rw [List.map_append, List.sum_append]
        have hlen_split : (work ++ acc).length = work.length + acc.length := List.length_append
        have hw_enc : (encodeNatListBin work).length ≤ 6 * n + 1 := by
          rw [encodeNatListBin_length]; omega
        have ha_enc : (encodeNatListBin acc).length ≤ 6 * n + 1 := by
          rw [encodeNatListBin_length]; omega
        have hst : (encState work acc).length ≤ 18 * n + 4 := by
          unfold encState
          rw [pairWord_length]
          omega
        exact ⟨hst, fun y hy => hbL.2.2 y (List.mem_append_left acc hy)⟩
      have hx_ge2 : 2 ≤ x := hge_w x (by rw [hwork]; simp)
      have hx_leN : x ≤ N := hlen_bounds.2 x (by rw [hwork]; simp)
      have hx_or := horacle x hx_ge2 hx_leN
      have hpair_in_len : (pairWord (encState work acc) (countWord (f x))).length ≤ maxLen := by
        rw [pairWord_length]
        dsimp only [maxLen]
        omega
      let ok := splitStepOk (f x) x
      have hstep_eq : splitStep (pairWord (encState work acc) (countWord (f x))) =
          splitStepEmit (splitStepNextWork ok (f x) x rest) (splitStepNextAcc ok x acc) := by
        unfold splitStep splitStepDecoded splitStepElse
        simp only [unpairWord_pairWord, countWord_isEmpty_false, cond_false,
          decState_encState, bval_countWord, hwork, ok]
      by_cases hok : 2 ≤ f x ∧ f x < x ∧ f x ∣ x
      · have hok_true : ok = true := splitStepOk_iff.mpr hok
        obtain ⟨hq2, _, _⟩ := proper_div_quot_bounds hok.1 hok.2.1 hok.2.2
        have hnw : splitStepNextWork ok (f x) x rest = f x :: (x / f x) :: rest := by
          simp [splitStepNextWork, hok_true]
        have hna : splitStepNextAcc ok x acc = acc := by simp [splitStepNextAcc, hok_true]
        have hfx_ge2 : 2 ≤ f x := hok.1
        have hfx_leN : f x ≤ N := by omega
        have hfx_or := horacle (f x) hfx_ge2 hfx_leN
        let work' := f x :: (x / f x) :: rest
        have hstep_false : splitStep (pairWord (encState work acc) (countWord (f x))) =
            false :: pairWord (encState work' acc) (countWord (f x)) := by
          rw [hstep_eq, hnw, hna]
          rfl
        have hprod' : (work' ++ acc).prod = N := by
          have hmul : f x * (x / f x) = x := Nat.mul_div_cancel' hok.2.2
          rw [← hprod, hwork]
          simp only [work', List.cons_append, List.prod_cons]
          rw [← mul_assoc, hmul]
        have hge_w' : ∀ y ∈ work', 2 ≤ y := by
          intro y hy
          simp only [work', List.mem_cons] at hy
          rcases hy with rfl | rfl | hy
          · exact hfx_ge2
          · exact hq2
          · exact hge_w y (by rw [hwork]; simp [hy])
        have hge_L' : ∀ y ∈ work' ++ acc, 2 ≤ y := by
          intro y hy
          rw [List.mem_append] at hy
          rcases hy with hy | hy
          · exact hge_w' y hy
          · exact hge_a y hy
        have hbL' := list_len_bounds_of_prod hN hge_L' hprod'
        have hsum' : ((work' ++ acc).map (fun a => (countWord a).length)).sum =
            (work'.map (fun a => (countWord a).length)).sum +
            (acc.map (fun a => (countWord a).length)).sum := by
          rw [List.map_append, List.sum_append]
        have hlen' : (work' ++ acc).length = work'.length + acc.length := List.length_append
        have hst'_len : (encState work' acc).length ≤ 18 * n + 4 := by
          have hw' : (encodeNatListBin work').length ≤ 6 * n + 1 := by
            rw [encodeNatListBin_length]; omega
          have ha' : (encodeNatListBin acc).length ≤ 6 * n + 1 := by
            rw [encodeNatListBin_length]; omega
          unfold encState
          rw [pairWord_length]
          omega
        have hmid_len : (pairWord (encState work' acc) (countWord (f x))).length ≤ maxLen := by
          rw [pairWord_length]
          dsimp only [maxLen]
          omega
        have hinv' : acc.reverse ++ work'.flatMap (canonSplit f) = canonSplit f N := by
          rw [← hinv, hwork]
          simp only [work', List.flatMap_cons]
          congr 1
          rw [canonSplit_eq hx_ge2, if_pos hok, List.append_assoc]
        have htn : treeNodes f x = 1 + treeNodes f (f x) + treeNodes f (x / f x) := by
          rw [treeNodes_eq hx_ge2, if_pos hok]
        let rem' := (work'.map (treeNodes f)).sum
        have hrem_succ : rem = rem' + 1 := by
          rw [hrem_eq, hwork]
          simp only [List.map_cons, List.sum_cons, htn]
          dsimp only [rem', work']
          simp only [List.map_cons, List.sum_cons]
          omega
        have hrem'_pos : 1 ≤ rem' := by
          dsimp only [rem', work']
          simp only [List.map_cons, List.sum_cons]
          have := treeNodes_pos f (f x)
          omega
        have hrec := ih rem' (by omega) hrem'_pos work' acc (f x) ((x / f x) :: rest) rfl rfl
          hge_w' hge_a hprod' hinv'
        have hloop_step : loopRuns (rem' + 1) (encState work acc) (countWord (f x)) outW maxLen := by
          right
          exact ⟨encState work' acc, countWord (f x), countWord (f (f x)), hstep_false,
            hpair_in_len, hmid_len, (by dsimp only [maxLen]; omega), hfx_or.1, hrec⟩
        exact hrem_succ ▸ hloop_step
      · have hok_false : ok = false := by
          cases h : ok
          · rfl
          · exfalso; exact hok (splitStepOk_iff.mp h)
        have hnw : splitStepNextWork ok (f x) x rest = rest := by
          simp [splitStepNextWork, hok_false]
        have hna : splitStepNextAcc ok x acc = x :: acc := by
          simp [splitStepNextAcc, hok_false]
        have htn : treeNodes f x = 1 := by
          rw [treeNodes_eq hx_ge2, if_neg hok]
        have hcanon_x : canonSplit f x = [x] := by
          rw [canonSplit_eq hx_ge2, if_neg hok]
        cases rest with
        | nil =>
          have hrem_one : rem = 1 := by
            rw [hrem_eq, hwork]; simp [htn]
          have hperm : (x :: acc).Perm (canonSplit f N) := by
            have hinv_eq : acc.reverse ++ [x] = canonSplit f N := by
              simpa [hwork, hcanon_x] using hinv
            rw [← hinv_eq]
            exact ((List.reverse_perm acc).symm.cons x).trans
              (by simpa using List.perm_append_comm (l₁ := [x]) (l₂ := acc.reverse))
          have hsort : insertionSort (x :: acc) = (canonSplit f N).mergeSort := by
            rw [insertionSort_eq_mergeSort]
            have h1 : ((x :: acc).mergeSort).Perm (canonSplit f N) :=
              (List.mergeSort_perm _ _).trans hperm
            have h2 : ((canonSplit f N).mergeSort).Perm (canonSplit f N) :=
              List.mergeSort_perm _ _
            have hp1 : ((x :: acc).mergeSort).Pairwise (· ≤ ·) := by
              have hw := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
                (fun a b c hab hbc => by
                  simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc)
                (fun a b => by rcases le_total a b with h | h <;> simp [h]) (x :: acc)
              exact hw.imp fun {a b} h => of_decide_eq_true h
            have hp2 : ((canonSplit f N).mergeSort).Pairwise (· ≤ ·) := by
              have hw := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
                (fun a b c hab hbc => by
                  simp only [decide_eq_true_eq] at hab hbc ⊢; exact le_trans hab hbc)
                (fun a b => by rcases le_total a b with h | h <;> simp [h]) (canonSplit f N)
              exact hw.imp fun {a b} h => of_decide_eq_true h
            exact (h1.trans h2.symm).eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hp1 hp2
          have hstep_true : splitStep (pairWord (encState work acc) (countWord (f x))) =
              true :: outW := by
            rw [hstep_eq, hnw, hna]
            simp [splitStepEmit, hsort, outW]
          rw [hrem_one]
          left
          exact ⟨hstep_true, hpair_in_len, houtW_len⟩
        | cons y rest' =>
          have hy_ge2 : 2 ≤ y := hge_w y (by rw [hwork]; simp)
          have hy_leN : y ≤ N := hlen_bounds.2 y (by rw [hwork]; simp)
          have hy_or := horacle y hy_ge2 hy_leN
          let work' := y :: rest'
          let acc' := x :: acc
          have hstep_false : splitStep (pairWord (encState work acc) (countWord (f x))) =
              false :: pairWord (encState work' acc') (countWord y) := by
            rw [hstep_eq, hnw, hna]
            rfl
          have hprod' : (work' ++ acc').prod = N := by
            rw [← hprod, hwork]
            simp only [work', acc', List.cons_append]
            simpa [List.prod_cons, List.prod_append] using
              (show (y :: (rest' ++ [x] ++ acc)).prod = x * (y * (rest' ++ acc).prod) by
                simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_one]; ring)
          have hge_w' : ∀ z ∈ work', 2 ≤ z := fun z hz => hge_w z (by rw [hwork]; exact List.mem_cons_of_mem x hz)
          have hge_a' : ∀ z ∈ acc', 2 ≤ z := by
            intro z hz
            simp only [acc', List.mem_cons] at hz
            rcases hz with rfl | hz
            · exact hx_ge2
            · exact hge_a z hz
          have hst'_len : (encState work' acc').length ≤ 18 * n + 4 := by
            have hgeL' : ∀ z ∈ work' ++ acc', 2 ≤ z := by
              intro z hz; rw [List.mem_append] at hz; rcases hz with hz | hz
              · exact hge_w' z hz
              · exact hge_a' z hz
            have hbL' := list_len_bounds_of_prod hN hgeL' hprod'
            have hsum' : ((work' ++ acc').map (fun a => (countWord a).length)).sum =
                (work'.map (fun a => (countWord a).length)).sum +
                (acc'.map (fun a => (countWord a).length)).sum := by
              rw [List.map_append, List.sum_append]
            have hlen' : (work' ++ acc').length = work'.length + acc'.length := List.length_append
            have hw' : (encodeNatListBin work').length ≤ 6 * n + 1 := by
              rw [encodeNatListBin_length]; omega
            have ha' : (encodeNatListBin acc').length ≤ 6 * n + 1 := by
              rw [encodeNatListBin_length]; omega
            unfold encState; rw [pairWord_length]; omega
          have hmid_len : (pairWord (encState work' acc') (countWord y)).length ≤ maxLen := by
            rw [pairWord_length]; dsimp only [maxLen]; omega
          have hinv' : acc'.reverse ++ work'.flatMap (canonSplit f) = canonSplit f N := by
            rw [← hinv, hwork]
            simp [work', acc', hcanon_x, List.append_assoc]
          let rem' := (work'.map (treeNodes f)).sum
          have hrem_succ : rem = rem' + 1 := by
            rw [hrem_eq, hwork]
            simp only [List.map_cons, List.sum_cons, htn]
            dsimp only [rem', work']
            simp only [List.map_cons, List.sum_cons]
            omega
          have hrem'_pos : 1 ≤ rem' := by
            dsimp only [rem', work']
            simp only [List.map_cons, List.sum_cons]
            have := treeNodes_pos f y
            omega
          have hrec := ih rem' (by omega) hrem'_pos work' acc' y rest' rfl rfl
            hge_w' hge_a' hprod' hinv'
          have hloop_step : loopRuns (rem' + 1) (encState work acc) (countWord (f x)) outW maxLen := by
            right
            exact ⟨encState work' acc', countWord y, countWord (f y), hstep_false,
              hpair_in_len, hmid_len, (by dsimp only [maxLen]; omega), hy_or.1, hrec⟩
          exact hrem_succ ▸ hloop_step
  have hN_or := horacle N hN le_rfl
  let rem0 := treeNodes f N
  have hrem0_pos : 1 ≤ rem0 := treeNodes_pos f N
  have hrec0 := hdfs rem0 hrem0_pos [N] [] N [] rfl (by simp [rem0])
    (fun y hy => by simp at hy; omega) (fun _ hy => by simp at hy)
    (by simp) (by simp)
  have hstep1 : splitStep (pairWord (countWord N) []) =
      false :: pairWord (encState [N] []) (countWord N) := by
    unfold splitStep splitStepDecoded
    simp only [unpairWord_pairWord, List.isEmpty_nil, cond_true, bval_countWord]
  have hpair0_len : (pairWord (countWord N) []).length ≤ maxLen := by
    rw [pairWord_length, List.length_nil]
    have hcwN := countWord_length_of_pos (by omega : 1 ≤ N)
    change (countWord N).length = n at hcwN
    dsimp only [maxLen]; omega
  have hmid0_len : (pairWord (encState [N] []) (countWord N)).length ≤ maxLen := by
    have hcwN : (countWord N).length = n := countWord_length_of_pos (by omega : 1 ≤ N)
    have hencN : (encodeNatListBin [N]).length = 2 * n + 3 := by
      rw [encodeNatListBin_length]; simp [hcwN]
    have henc0 : (encodeNatListBin []).length = 1 := by
      rw [encodeNatListBin_length]; simp
    have hst0 : (encState [N] []).length = 4 * n + 8 := by
      unfold encState; rw [pairWord_length, hencN, henc0]; omega
    rw [pairWord_length, hst0, hcwN]
    dsimp only [maxLen]; omega
  have hloop_full : loopRuns (rem0 + 1) (countWord N) [] outW maxLen := by
    right
    exact ⟨encState [N] [], countWord N, countWord (f N), hstep1,
      hpair0_len, hmid0_len, (by dsimp only [maxLen]; omega), hN_or.1, hrec0⟩
  have hrun_M := hloop_inst (rem0 + 1) maxLen (countWord N) outW (by omega) hloop_full
  have hrem0_le : rem0 + 1 ≤ 2 * n := by
    have h1 := treeNodes_add_one f N hN
    have hc := canonSplit_prod_ge2 f N hN
    have hb := list_len_bounds_of_prod hN hc.2 hc.1
    change rem0 + 1 = 2 * (canonSplit f N).length at h1
    omega
  have hK_sp1 : K_loop * (Kd + 63) ^ K_loop + K_loop * (Kd + 1) + 1 ≤ K_sp := by
    dsimp [K_sp]; omega
  have hK_sp2 : K_loop * max Kd 1 ≤ K_sp := by
    dsimp [K_sp]; omega
  have htime_le : ((rem0 + 1 : ℕ) : ℝ) * (polyBound K_loop maxLen + (K_loop : ℝ) * (τO + σO + 1)) ≤
      (2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) := by
    have ht1 := driver_time_arith Kd K_loop K_sp K_tm n (rem0 + 1) hK_loop1 hrem0_le hn2 hK_sp1 hK_sp2 rfl
    have ht2 : (2 : ℝ) ^ ((K_tm : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) ≤
        (2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ?_
      refine div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast le_max_right K_sp K_tm
    exact le_trans ht1 ht2
  have hspace_le : polyBound K_loop maxLen + (K_loop : ℝ) * (σO + 1) ≤ polyBound K n := by
    have hs1 := driver_space_arith Kd K_loop n K_sp hK_loop1 hK_sp1 hK_sp2
    have hs2 : polyBound K_sp n ≤ polyBound K n := by
      unfold polyBound
      have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      exact mul_le_mul (by exact_mod_cast le_max_left K_sp K_tm)
        (pow_le_pow_right₀ hbase (le_max_left K_sp K_tm)) (by positivity) (by positivity)
    exact le_trans hs1 hs2
  exact DetDLP.MachineComposition.runsWithin_mono hrun_M htime_le hspace_le

end DetDLP

theorem solution
    (f : ℕ → ℕ) (Md : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ)
    (hd : ∀ N : ℕ, 2 ≤ N →
      let n := DetDLP.bitLen (N+1)
      DetDLP.RunsWithin Md od (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord N)
        (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord (f N))
        ((2 : ℝ)^((Kd : ℝ)*n/Real.sqrt (DetDLP.logSafe n))) (DetDLP.polyBound Kd n)) :
    ∃ (M : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := DetDLP.bitLen (N+1)
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x/d) else [x])
        DetDLP.RunsWithin M out (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord N)
          (DetDLP.encodeNatListBin ((split n N).mergeSort))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (DetDLP.logSafe (n : ℝ)))) (DetDLP.polyBound K n) :=
  DetDLP.factor_splitting_driver_machine_proved f Md od Kd hd
