-- Prove2me | solution 1 for BipHamCount.Deterministic.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:27:34.506543+00:00
-- url     : https://prove2.me/submissions/00a73f19-1101-4c3f-9bc1-07d116ca9963

import Definitions.Def_BipHamCount_Deterministic_Programs
import Theorems.Thm_BipHamCount_Deterministic_lemma_4_3
import Theorems.Thm_BipHamCount_Deterministic_lemma_4_4
import Theorems.Thm_BipHamCount_Deterministic_smallTerms_index_enumeration
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.List.Sublists
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic

namespace BipHamCount.Deterministic
private def chooseSets_spec {m : ℕ} (xs : List (Fin m)) (q s : ℕ) :=
  smallTerms_index_enumeration.1 m xs q s
private theorem labelPairs_spec {m : ℕ} (xs : List (Fin m)) (h : xs.Nodup) (s : ℕ) :
    ((labelPairs xs).run s).1.Nodup ∧
      ∀ t : Finset (Fin m) × Finset (Fin m),
        t ∈ ((labelPairs xs).run s).1 ↔ t.1 ∪ t.2 = xs.toFinset :=
  ⟨(smallTerms_index_enumeration.2.1 m xs s h).1,(smallTerms_index_enumeration.2.1 m xs s h).2.1⟩
end BipHamCount.Deterministic

open CapacitatedAssort.General
namespace BipHamCount.Deterministic
private def suffixLoop {m : ℕ} (lo : ℕ) (xs acc : List (Fin m)) : Work (List (Fin m)) := do
  let mut out := acc
  for i in xs do
    charge (m+3)
    if lo ≤ i.val then out := i::out
  return out

private theorem suffixLoop_run {m : ℕ} (lo : ℕ) (xs acc : List (Fin m)) (s : ℕ) :
    (suffixLoop lo xs acc).run s = ((xs.filter (fun i => decide (lo ≤ i.val))).reverse ++ acc,
      s+(m+3)*xs.length) := by
  induction xs generalizing acc s with
  | nil => change (acc,s) = _; simp
  | cons i xs ih =>
    by_cases hi : lo ≤ i.val
    · have h : (suffixLoop lo (i::xs) acc).run s = (suffixLoop lo xs (i::acc)).run (s+(m+3)) := by
        simp [suffixLoop,charge,StateT.run_bind,hi]
      rw [h,ih]; simp [hi,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · have h : (suffixLoop lo (i::xs) acc).run s = (suffixLoop lo xs acc).run (s+(m+3)) := by
        simp [suffixLoop,charge,StateT.run_bind,hi]
      rw [h,ih]; simp [hi,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem suffix_run {m : ℕ} (lo s : ℕ) :
    (suffix (m := m) lo).run s = ((List.finRange m).filter (fun i => decide (lo ≤ i.val)),
      s+(4*m+1)+(m+3)*m) := by
  change (suffixLoop lo (List.finRange m).reverse []).run (s+(4*m+1)) = _
  rw [suffixLoop_run]
  simp [List.filter_reverse]
end BipHamCount.Deterministic

open CapacitatedAssort.General
open Finset
open scoped BigOperators
namespace BipHamCount.Deterministic

theorem chooseSets_perm_layer {m : ℕ} (q s : ℕ) :
    ((chooseSets (List.finRange m) q).run s).1.Perm
      (((Finset.univ : Finset (Fin m)).powersetCard q).toList) := by
  classical
  let xs := List.finRange m
  let sets := (Finset.univ : Finset (Fin m)).powersetCard q
  let gen := (xs.sublistsLen q).map List.toFinset
  apply (chooseSets_spec xs q s).1.trans
  have sub : sets.toList ⊆ gen := by
    intro U hU
    have hcard : U.card=q := (Finset.mem_powersetCard.mp (Finset.mem_toList.mp hU)).2
    let vs := xs.filter fun v => decide (v ∈ U)
    have he : vs.toFinset = U := by ext v; simp [vs,xs]
    have hn : vs.Nodup := (List.nodup_finRange m).filter _
    have hl : vs.length=q := by rw [←List.toFinset_card_of_nodup hn,he,hcard]
    exact List.mem_map.mpr ⟨vs,List.mem_sublistsLen.mpr ⟨List.filter_sublist,hl⟩,he⟩
  obtain ⟨z,hz,ht⟩ := List.subperm_iff.mp (sets.nodup_toList.subperm sub)
  have hl : gen.length = sets.toList.length := by simp [gen,sets,xs, Finset.card_powersetCard]
  have he := ht.eq_of_length (hz.length_eq.trans hl).symm
  exact (he ▸ hz).symm

noncomputable def pairsOver {m : ℕ} (U : Finset (Fin m)) : Finset (Finset (Fin m) × Finset (Fin m)) :=
  Finset.univ.filter (fun p => p.1 ∪ p.2 = U)

theorem labelPairs_perm_layer {m : ℕ} (U : Finset (Fin m)) (s : ℕ) :
    ((labelPairs (U.sort (· ≤ ·))).run s).1.Perm (pairsOver U).toList := by
  classical
  obtain ⟨hn,hm⟩ := labelPairs_spec (U.sort (· ≤ ·)) (U.sort_nodup _) s
  apply List.perm_of_nodup_nodup_toFinset_eq hn (Finset.nodup_toList _)
  ext p
  simp [hm, pairsOver]

theorem sum_pair_layers {m : ℕ} (k : ℕ) (f : Finset (Fin m) × Finset (Fin m) → ℤ) :
    (∑ q ∈ range (min k m+1), ∑ U ∈ (Finset.univ : Finset (Fin m)).powersetCard q,
      ∑ p ∈ pairsOver U, f p) =
      ∑ X ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ Y ∈ (Finset.univ : Finset (Fin m)).powerset.filter (fun Y => (X ∪ Y).card ≤ k), f (X,Y) := by
  classical
  simp only [pairsOver, Finset.sum_filter]
  rw [show (Finset.univ : Finset (Fin m)).powerset = Finset.univ by ext; simp]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin m)).powersetCard _)
    (t := (Finset.univ : Finset (Finset (Fin m) × Finset (Fin m))))]
  rw [Finset.sum_comm]
  conv_rhs => rw [← Finset.sum_product', Finset.univ_product_univ]
  apply Finset.sum_congr rfl
  intro p hp
  let U := p.1 ∪ p.2
  have hsum (q : ℕ) : (∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard q,
      if p.1 ∪ p.2 = T then f p else 0) = if U.card=q then f p else 0 := by
    simp [U]
  simp_rw [hsum]
  have hU := Finset.card_le_univ U
  simp [Finset.mem_range, Nat.lt_succ_iff, U] at *
  aesop
end BipHamCount.Deterministic

open CapacitatedAssort.General
namespace BipHamCount.Deterministic

abbrev P (m : ℕ) := Finset (Fin m) × Finset (Fin m)
def visits {α : Type} (xs : List α) (z : ℤ) (step : α → ℤ → Work ℤ) : Work ℤ := do
  let mut out := z
  for x in xs do out ← step x out
  return out

private theorem visits_val {α : Type} (xs : List α) (z : ℤ) (s : ℕ) (f : α → ℤ)
    (step : α → ℤ → Work ℤ)
    (hf : ∀ x ∈ xs, ∀ z s, ((step x z).run s).1=z+f x) :
    ((visits xs z step).run s).1=z+(xs.map f).sum := by
  induction xs generalizing z s with
  | nil => change z=z+0; simp
  | cons x xs ih =>
    have h : (visits (x::xs) z step).run s =
        (visits xs ((step x z).run s).1 step).run ((step x z).run s).2 := by
      simp [visits,StateT.run_bind]; rfl
    rw [h,ih _ _ (fun a ha => hf _ (by simp [ha])),hf _ (by simp)]
    simp [add_assoc]

def pairStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ)
    (p : P m) (out : ℤ) : Work ℤ := do
  charge (2*(m+1)+1)
  let f ← computeF m A B v k p.1 p.2
  let s ← paritySign (p.1.card+p.2.card)
  let z ← zmul s f
  zadd out z

def unionStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ)
    (U : Finset (Fin m)) (out : ℤ) : Work ℤ := do
  charge (8*(m+1)^3)
  let pairs ← labelPairs (U.sort (· ≤ ·))
  visits pairs out (pairStep A B v k)

def layerStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ)
    (all : List (Fin m)) (q : ℕ) (out : ℤ) : Work ℤ := do
  charge 1
  let us ← chooseSets all q
  visits us out (unionStep A B v k)

theorem smallTerms_unroll (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    smallTerms m A B v k = (do
      let all ← suffix (m:=m) 0
      charge (4*(min k m+1)+1)
      visits (List.range (min k m+1)) 0 (layerStep A B v k all)) := by
  rfl

theorem pairStep_run {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ)
    (p : P m) (out : ℤ) (s : ℕ)
    (h : ∀ X Y s, ((computeF m A B v k X Y).run s).1=Fval A B v k X Y) :
    ((pairStep A B v k p out).run s).1=out+(-1)^(p.1.card+p.2.card)*Fval A B v k p.1 p.2 := by
  change out+(if (p.1.card+p.2.card)%2=0 then (1:ℤ) else -1)*
      ((computeF m A B v k p.1 p.2).run (s+(2*(m+1)+1))).1 = _
  simp only [h, neg_one_pow_eq_ite, Nat.even_iff]

open Finset
open scoped BigOperators
theorem smallTerms_correct_from_F (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (s : ℕ) (hF : ∀ X Y s, ((computeF m A B v k X Y).run s).1=Fval A B v k X Y) :
    ((smallTerms m A B v k).run s).1 =
      ∑ X ∈ (Finset.univ : Finset (Fin m)).powerset,
        ∑ Y ∈ Finset.univ.powerset.filter (fun Y : Finset (Fin m) => (X ∪ Y).card ≤ k),
          (-1:ℤ)^(X.card+Y.card)*Fval A B v k X Y := by
  classical
  let f := fun p : P m => (-1:ℤ)^(p.1.card+p.2.card)*Fval A B v k p.1 p.2
  let g := fun U : Finset (Fin m) => ∑ p ∈ pairsOver U, f p
  let z := fun q => ∑ U ∈ (Finset.univ : Finset (Fin m)).powersetCard q, g U
  have hu U acc st : ((unionStep A B v k U acc).run st).1=acc+g U := by
    let pts := (labelPairs (U.sort (· ≤ ·))).run (st+8*(m+1)^3)
    change ((visits pts.1 acc (pairStep A B v k)).run pts.2).1 = _
    rw [visits_val _ _ _ f _ (fun p _ y r => pairStep_run A B v k p y r hF)]
    rw [((labelPairs_perm_layer U _).map f).sum_eq, Finset.sum_map_toList]
  have hq q acc st : ((layerStep A B v k (List.finRange m) q acc).run st).1=acc+z q := by
    let us := (chooseSets (List.finRange m) q).run (st+1)
    change ((visits us.1 acc (unionStep A B v k)).run us.2).1 = _
    rw [visits_val _ _ _ g _ (fun U _ => hu U)]
    rw [((chooseSets_perm_layer q _).map g).sum_eq, Finset.sum_map_toList]
  rw [smallTerms_unroll]
  let all := (suffix (m:=m) 0).run s
  change ((visits (List.range (min k m+1)) 0 (layerStep A B v k all.1)).run
    (all.2 + (4*(min k m+1)+1))).1 = _
  have ha : all.1 = List.finRange m := by simp [all,suffix_run]
  rw [ha,visits_val _ _ _ z _ (fun q _ => hq q),zero_add,
    ←List.sum_toFinset z List.nodup_range]
  rw [show (List.range (min k m+1)).toFinset=Finset.range (min k m+1) by ext i; simp]
  simpa [z,g,f] using sum_pair_layers k f
end BipHamCount.Deterministic

open CapacitatedAssort.General
namespace WorkCalc
def Fixed {α : Type} (p : Work α) : Prop := ∃ x c, ∀ s, p.run s = (x,s+c)

theorem eval {α : Type} {p : Work α} (h : Fixed p) (s : ℕ) :
    p.run s = ((p.run 0).1,s+(p.run 0).2) := by
  obtain ⟨x,c,h⟩ := h
  simp only [h,Nat.zero_add]

theorem ret {α : Type} (x : α) : Fixed (pure x) := ⟨x,0,fun _ => rfl⟩
theorem tick (n : ℕ) : Fixed (charge n) := ⟨(),n,fun _ => rfl⟩
theorem bind {α β : Type} {a : Work α} {f : α → Work β}
    (ha : Fixed a) (hf : ∀ x, Fixed (f x)) : Fixed (a >>= f) := by
  obtain ⟨x,c,h⟩ := ha
  obtain ⟨y,d,j⟩ := hf x
  refine ⟨y,c+d,fun s => ?_⟩
  change (f (a.run s).1).run (a.run s).2 = _
  rw [h]
  change (f x).run (s+c) = _
  rw [j,Nat.add_assoc]

theorem list {α β : Type} (xs : List α) (b : β) (f : α → β → Work (ForInStep β))
    (hf : ∀ x y, Fixed (f x y)) : Fixed (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa using ret b
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bind (hf x b)
    intro h
    cases h with
    | done b => exact ret _
    | yield b => exact ih b

theorem array {α β : Type} (xs : Array α) (b : β) (f : α → β → Work (ForInStep β))
    (hf : ∀ x y, Fixed (f x y)) : Fixed (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact list _ _ _ hf

end WorkCalc

open CapacitatedAssort.General WorkCalc
namespace BipHamCount.Deterministic

private lemma zadd_fixed (a b : ℤ) : Fixed (zadd a b) := by
  unfold zadd
  exact WorkCalc.bind (tick _) (fun _ => ret _)
private lemma zsub_fixed (a b : ℤ) : Fixed (zsub a b) := by
  unfold zsub
  exact WorkCalc.bind (tick _) (fun _ => ret _)
private lemma zmul_fixed (a b : ℤ) : Fixed (zmul a b) := by
  unfold zmul
  exact WorkCalc.bind (tick _) (fun _ => ret _)

theorem padd_fixed (a b : ZPoly) : Fixed (padd a b) := by unfold padd; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
theorem pmul_fixed (a b : ZPoly) : Fixed (pmul a b) := by unfold pmul; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
theorem pneg_fixed (a : ZPoly) : Fixed (pneg a) := by unfold pneg; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)

private theorem parity_fixed (e : ℕ) : Fixed (paritySign e) :=
  WorkCalc.bind (WorkCalc.tick _) (fun _ => WorkCalc.ret _)

private theorem matRead_fixed {R : Type} (O : RingOps R) (M : Array (Array R)) (i j : ℕ) :
    Fixed (matRead O M i j) := WorkCalc.bind (WorkCalc.tick _) (fun _ => WorkCalc.ret _)

theorem berkCoeffs_fixed {R : Type} (O : RingOps R)
    (hadd : ∀ x y, Fixed (O.add x y)) (hmul : ∀ x y, Fixed (O.mul x y)) (hneg : ∀ x, Fixed (O.neg x))
    (M : Array (Array R)) (n off : ℕ) : Fixed (berkCoeffs O M n off) := by
  have hr := matRead_fixed O M
  induction n generalizing off with
  | zero => unfold berkCoeffs; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
  | succ n ih => rw [berkCoeffs]; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)

theorem berkowitz_fixed {R : Type} (O : RingOps R)
    (hadd : ∀ x y, Fixed (O.add x y)) (hmul : ∀ x y, Fixed (O.mul x y)) (hneg : ∀ x, Fixed (O.neg x))
    (n : ℕ) (M : Array (Array R)) : Fixed (berkowitz O n M) := by
  have hc := berkCoeffs_fixed O hadd hmul hneg M n 0
  unfold berkowitz; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)

theorem computeW_fixed {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (X Y : Finset (Fin m)) (i : Fin m) :
    Fixed (computeW A B X Y i) := by unfold computeW; (repeat' first | with_reducible assumption | with_reducible solve_by_elim (maxDepth := 2) only [*] | with_reducible exact zadd_fixed _ _ | with_reducible exact zsub_fixed _ _ | with_reducible exact zmul_fixed _ _ | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)

end BipHamCount.Deterministic

open CapacitatedAssort.General WorkCalc
namespace BipHamCount.Deterministic
set_option maxHeartbeats 1600000 in
theorem computeF_fixed (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ)
    (X Y : Finset (Fin m)) : Fixed (computeF m A B v k X Y) := by
  have hw := computeW_fixed A B X Y
  have hd := berkowitz_fixed polyOps padd_fixed pmul_fixed pneg_fixed m
  have hp (e : ℕ) : Fixed (paritySign e) := WorkCalc.bind (tick _) (fun _ => ret _)
  have ha (a b : ℤ) : Fixed (zadd a b) := WorkCalc.bind (tick _) (fun _ => ret _)
  have hm (a b : ℤ) : Fixed (zmul a b) := WorkCalc.bind (tick _) (fun _ => ret _)
  unfold computeF
  repeat' first
    | with_reducible exact WorkCalc.tick _
    | with_reducible exact WorkCalc.ret _
    | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_)
    | with_reducible refine WorkCalc.bind ?_ (fun x => ?_)
    | with_reducible exact hw _
    | with_reducible exact hd _
    | with_reducible exact ha _ _
    | with_reducible exact hp _
    | with_reducible exact hm _ _
end BipHamCount.Deterministic


open Finset BipHamCount.Deterministic
open scoped BigOperators

private lemma abs_sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ b) : (∑ i ∈ s, f i).natAbs ≤ s.card * b := by
  apply (Int.natAbs_sum_le s f).trans
  simpa using Finset.sum_le_sum h

private lemma abs_prod_bound {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ b) : (∏ i ∈ s, f i).natAbs ≤ b^s.card := by
  change Int.natAbsHom (∏ i ∈ s, f i) ≤ _
  rw [map_prod]
  simpa using Finset.prod_le_prod' h

private lemma abs_minor {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (S T : Finset (Fin m)) : (minor A S T).natAbs ≤ m.factorial := by
  classical
  unfold minor
  split
  next h =>
    rw [Matrix.det_apply']
    apply (abs_sum_bound _ _ 1 ?_).trans
    · simpa [Fintype.card_perm] using Nat.factorial_le (show S.card ≤ m by simpa using card_le_univ S)
    · intro π hπ
      have hu (u : ℤˣ) : (u : ℤ).natAbs = 1 := by rcases Int.units_eq_one_or u with rfl|rfl <;> simp
      simp only [Int.natAbs_mul,Int.cast_id,hu,one_mul]
      apply (abs_prod_bound _ _ 1 ?_).trans (by simp)
      intro i _
      change (A _ _).natAbs ≤ 1
      rcases hA (S.orderEmbOfFin rfl (π i)) (T.orderEmbOfFin h i) with ha|ha <;> simp [ha]
  next h => simp

private lemma abs_weight {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (hB : ZeroOne B) (X Y : Finset (Fin m)) (i : Fin m) :
    (w A B X Y i).natAbs ≤ (m+1)^2 := by
  have bound (s : Finset (Fin m)) (f : Fin m → ℤ) (hf : ∀ j, f j = 0 ∨ f j = 1)
      (hs : s.card ≤ m) : (∑ j ∈ s, f j).natAbs ≤ m+1 := by
    apply (abs_sum_bound _ _ 1 ?_).trans (by omega)
    intro j _; rcases hf j with hj|hj <;> simp [hj]
  rw [w,Int.natAbs_mul,pow_two]
  exact Nat.mul_le_mul (bound X _ (hA i) (by simpa using card_le_univ X))
    (bound Y _ (fun j => hB j i) (by simpa using card_le_univ Y))

theorem fval_abs_bound {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (hB : ZeroOne B) (v : Fin m) (k : ℕ) (X Y : Finset (Fin m)) :
    (Fval A B v k X Y).natAbs ≤ 2^m * (2^m * (m.factorial * m.factorial * ((m+1)^2)^m)) := by
  classical
  have count (S : Finset (Finset (Fin m))) : S.card ≤ 2^m := by simpa using card_le_univ S
  unfold Fval
  apply (abs_sum_bound _ _ _ ?_).trans (Nat.mul_le_mul_right _ (count _))
  intro S _
  apply (abs_sum_bound _ _ _ ?_).trans (Nat.mul_le_mul_right _ (count _))
  intro T _
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
  apply Nat.mul_le_mul (Nat.mul_le_mul (abs_minor _ hA _ _) (abs_minor _ hB _ _))
  apply (abs_prod_bound _ _ _ (fun i _ => abs_weight A B hA hB X Y i)).trans
  exact Nat.pow_le_pow_right (by positivity) (by simpa using card_le_univ S)

open CapacitatedAssort.General
namespace BipHamCount.Deterministic
def Fmax (m : ℕ) := 2^m * (2^m * (m.factorial*m.factorial*((m+1)^2)^m))
private theorem total_mag (m : ℕ) : 4^m*Fmax m ≤ 2^(4*(m+1)^2) := by
  have hb : m+1 ≤ 2^(m+1) := (Nat.lt_two_pow_self).le
  have hfac : m.factorial ≤ (2^(m+1))^m := m.factorial_le_pow.trans
    (Nat.pow_le_pow_left (by omega) _)
  unfold Fmax
  calc
    _ ≤ 4^m * (2^m * (2^m * (((2^(m+1))^m) * ((2^(m+1))^m) * (((2^(m+1))^2)^m)))) := by gcongr
    _ = 2^(2*m + m + m + (m+1)*m + (m+1)*m + ((m+1)*2)*m) := by
        rw [show (4:ℕ)=2^2 by decide]
        simp only [pow_add,pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by nlinarith)

def Spec (m : ℕ) (step : ℤ → Work ℤ) (n cost : ℕ) : Prop :=
  ∀ l acc s, l+n ≤ 4^m → acc.natAbs ≤ l*Fmax m →
    (step acc |>.run s).1.natAbs ≤ (l+n)*Fmax m ∧ (step acc |>.run s).2 ≤ s+cost

theorem visits_spec {α : Type} (m : ℕ) (xs : List α) (step : α → ℤ → Work ℤ)
    (count cost : α → ℕ) (h : ∀ x ∈ xs, Spec m (step x) (count x) (cost x)) :
    Spec m (fun acc => visits xs acc step) (xs.map count).sum (xs.map cost).sum := by
  intro l acc s hl ha
  induction xs generalizing l acc s with
  | nil => change acc.natAbs ≤ (l+0)*Fmax m ∧ s ≤ s+0; simpa using ha
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons] at hl ⊢
    let r := (step x acc).run s
    obtain ⟨h1,h2⟩ := h x (by simp) l acc s (by omega) ha
    have ht := ih (fun y hy => h y (by simp [hy])) (l+count x) r.1 r.2 (by omega) h1
    have he : (visits (x::xs) acc step).run s = (visits xs r.1 step).run r.2 := by
      simp [visits,StateT.run_bind,r]; rfl
    rw [he]
    exact ⟨by simpa [Nat.add_assoc] using ht.1, by exact ht.2.trans (by change r.2 ≤ s+cost x at h2; omega)⟩

private theorem size_mag (m z : ℕ) (h : z ≤ 4^m * Fmax m) : z.size ≤ 4*(m+1)^2+1 := by
  apply Nat.size_le.mpr
  exact (h.trans (total_mag m)).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem pair_spec (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (k t : ℕ) (p : P m)
    (hv : ∀ X Y s, ((computeF m A B v k X Y).run s).1 = Fval A B v k X Y)
    (hc : ∀ X Y s, ((computeF m A B v k X Y).run s).2 ≤ s+t) :
    Spec m (pairStep A B v k p) 1 (t+1000*(m+1)^4) := by
  intro l acc s hl ha
  let n := p.1.card+p.2.card
  let sig : ℤ := if n%2=0 then 1 else -1
  let r := (computeF m A B v k p.1 p.2).run (s+(2*(m+1)+1))
  have hr : r.1.natAbs ≤ Fmax m := by
    change ((computeF _ _ _ _ _ _ _).run _).1.natAbs ≤ _
    rw [hv]; exact fval_abs_bound _ _ hA hB _ _ _ _
  have hs : sig.natAbs=1 := by dsimp [sig]; split <;> decide
  have hs' : (sig*r.1).natAbs=r.1.natAbs := by simp [Int.natAbs_mul,hs]
  constructor
  · change (acc+sig*r.1).natAbs ≤ _
    exact (Int.natAbs_add_le _ _).trans (by rw [hs',Nat.add_mul,one_mul]; omega)
  · change r.2+(n.size+1)^2+(sig.natAbs.size+r.1.natAbs.size+1)^2+
      (acc.natAbs.size+(sig*r.1).natAbs.size+1)^2 ≤ _
    rw [hs,hs']
    have hrc : r.2 ≤ s+(2*(m+1)+1)+t := hc _ _ _
    have hsacc := size_mag m acc.natAbs (ha.trans (Nat.mul_le_mul_right _ (by omega)))
    have hsr := size_mag m r.1.natAbs (hr.trans (Nat.le_mul_of_pos_left _ (by positivity)))
    have hn : n.size ≤ 2*m := by
      have h1 : p.1.card ≤ m := by simpa using Finset.card_le_univ p.1
      have h2 : p.2.card ≤ m := by simpa using Finset.card_le_univ p.2
      have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
      dsimp [n] at *; omega
    have h1 := Nat.pow_le_pow_left (by omega : n.size+1 ≤ 2*m+1) 2
    have h2 := Nat.pow_le_pow_left (by change 1+r.1.natAbs.size+1 ≤ _; omega :
      (1:ℕ).size+r.1.natAbs.size+1 ≤ 4*(m+1)^2+3) 2
    have h3 := Nat.pow_le_pow_left (by omega : acc.natAbs.size+r.1.natAbs.size+1 ≤ 8*(m+1)^2+3) 2
    nlinarith
end BipHamCount.Deterministic

open scoped BigOperators
open CapacitatedAssort.General Finset
namespace BipHamCount.Deterministic
private theorem const_count {α : Type*} (xs : List α) (d : ℕ) :
    (xs.map (fun _ => d)).sum = xs.length*d := by induction xs <;> simp_all [add_mul,add_comm]

private theorem spec_mono {m n c d} {step : ℤ → Work ℤ} (h : Spec m step n c) (hle : c ≤ d) :
    Spec m step n d := fun l acc s hl ha => ⟨(h l acc s hl ha).1,(h l acc s hl ha).2.trans (by omega)⟩

theorem union_spec {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k t : ℕ)
    (hpair : ∀ p, Spec m (pairStep A B v k p) 1 (t+1000*(m+1)^4)) (U : Finset (Fin m)) :
    Spec m (unionStep A B v k U) (3^U.card) (3^U.card*(t+2000*(m+1)^4)) := by
  intro l acc s hl ha
  let s' := s+8*(m+1)^3
  let ps := (labelPairs (U.sort (· ≤ ·))).run s'
  have hh := (smallTerms_index_enumeration.2.1 m (U.sort (· ≤ ·)) s' (U.sort_nodup _)).2.2
  have hn : ps.1.length = 3^U.card := by simpa [ps] using hh.1
  have hc : ps.2 ≤ s' + (4*m+12)*3^U.card := by simpa [ps] using hh.2
  have h := visits_spec m ps.1 (pairStep A B v k) (fun _ => 1) (fun _ => t+1000*(m+1)^4)
    (fun p _ => hpair p)
  rw [const_count,const_count,hn,mul_one] at h
  obtain ⟨hv,hw⟩ := h l acc ps.2 hl ha
  change _ ∧ ((visits ps.1 acc (pairStep A B v k)).run ps.2).2 ≤ _
  refine ⟨hv,hw.trans ?_⟩
  have hx : 1 ≤ 3^U.card := Nat.one_le_pow _ _ (by decide)
  have hp : 8*(m+1)^3+(4*m+12) ≤ 1000*(m+1)^4 := by nlinarith [Nat.zero_le (m^4), Nat.zero_le (m^3), Nat.zero_le (m^2)]
  have hz := Nat.mul_le_mul_left (3^U.card) hp
  have hf := Nat.mul_le_mul_right (8*(m+1)^3) hx
  dsimp [s'] at hc
  nlinarith only [hc,hz,hf]

theorem layer_spec {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k t : ℕ)
    (hu : ∀ U, Spec m (unionStep A B v k U) (3^U.card) (3^U.card*(t+2000*(m+1)^4)))
    (q : ℕ) (hq : q ≤ m) :
    Spec m (layerStep A B v k (List.finRange m) q) (m.choose q*3^q)
      ((m.choose q*3^q)*(t+3000*(m+1)^4)) := by
  intro l acc s hl ha
  let us := (chooseSets (List.finRange m) q).run (s+1)
  have perm := chooseSets_perm_layer (m:=m) q (s+1)
  have hn : us.1.length = m.choose q := by simpa [us,Finset.card_powersetCard] using perm.length_eq
  have hc : us.2 ≤ s+1+(m+4)*(3*(m+1)*m.choose q+1) := by
    simpa [us] using (chooseSets_spec (List.finRange m) q (s+1)).2
  have hmem (U) (hU : U ∈ us.1) : U.card=q := by
    exact (Finset.mem_powersetCard.mp (Finset.mem_toList.mp (perm.mem_iff.mp hU))).2
  have h := visits_spec m us.1 (unionStep A B v k) (fun _ => 3^q)
    (fun _ => 3^q*(t+2000*(m+1)^4)) (fun U hU => by simpa [hmem U hU] using hu U)
  rw [const_count,const_count,hn] at h
  obtain ⟨hv,hw⟩ := h l acc us.2 hl ha
  refine ⟨hv,hw.trans ?_⟩
  have hq1 : 1 ≤ m.choose q := Nat.choose_pos hq
  have hq2 : 1 ≤ 3^q := Nat.one_le_pow _ _ (by decide)
  have hmul := Nat.mul_le_mul_left (m.choose q) hq2
  have base : (m+4)*(3*(m+1)+1)+1 ≤ 1000*(m+1)^4 := by nlinarith [Nat.zero_le (m^4), Nat.zero_le (m^3), Nat.zero_le (m^2)]
  have small := Nat.mul_le_mul_right (m+4+1) hq1
  have big := Nat.mul_le_mul_left (m.choose q) base
  have bigger := Nat.mul_le_mul_right (1000*(m+1)^4) hmul
  nlinarith only [hc,small,big,bigger]
end BipHamCount.Deterministic

open CapacitatedAssort.General Finset
open scoped BigOperators
namespace BipHamCount.Deterministic
private def visitsCount (m k : ℕ) := (∑ q ∈ range (min k m+1), m.choose q*3^q)
private theorem visitsCount_pos (m k : ℕ) : 1 ≤ visitsCount m k := by
  have h := Finset.single_le_sum (s:=range (min k m+1)) (f:=fun q => m.choose q*3^q)
    (fun i _ => Nat.zero_le _) (show 0∈range (min k m+1) by simp)
  simpa [visitsCount] using h
private theorem visitsCount_bound (m k : ℕ) : visitsCount m k ≤ 4^m := by
  calc
    _ ≤ ∑ q ∈ range (m+1), m.choose q*3^q := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    _ = (3+1)^m := by rw [add_pow]; simp [mul_comm]
    _ = _ := rfl

theorem smallTerms_cost_F {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (k t : ℕ)
    (hv : ∀ X Y s, ((computeF m A B v k X Y).run s).1 = Fval A B v k X Y)
    (hc : ∀ X Y s, ((computeF m A B v k X Y).run s).2 ≤ s+t) :
    ((smallTerms m A B v k).run 0).2 ≤ 
      (∑ q ∈ range (min k m+1), m.choose q*3^q)*(t+4000*(m+1)^4) := by
  let f := fun q => m.choose q*3^q
  let D := t+3000*(m+1)^4
  let N := visitsCount m k
  let qs := List.range (min k m+1)
  have hl := layer_spec A B v k t (union_spec A B v k t (pair_spec m A B hA hB v k t · hv hc))
  have hh := visits_spec m qs (layerStep A B v k (List.finRange m)) f (fun q => f q*D)
    (fun q hq => hl q (by have h : q < min k m+1 := List.mem_range.mp hq; omega))
  have he : qs.toFinset = range (min k m+1) := by ext x; simp [qs]
  have hc1 : (qs.map f).sum=N := by rw [← List.sum_toFinset f List.nodup_range,he]; rfl
  have hc2 : (qs.map (fun q => f q*D)).sum=N*D := by
    rw [←List.sum_toFinset _ List.nodup_range,he,←Finset.sum_mul]; rfl
  rw [hc1,hc2] at hh
  let s := 4*m+1+(m+3)*m+(4*(min k m+1)+1)
  have h := (hh 0 0 s (by simpa [N] using visitsCount_bound m k) (by simp)).2
  rw [smallTerms_unroll]
  let all := (suffix (m:=m) 0).run 0
  change ((visits qs 0 (layerStep A B v k all.1)).run (all.2+(4*(min k m+1)+1))).2 ≤ _
  have ha : all.1=List.finRange m := by simp [all,suffix_run]
  have hs : all.2+(4*(min k m+1)+1)=s := by simp [all,s,suffix_run]
  rw [ha,hs]
  apply h.trans
  change s+N*D ≤ N*(t+4000*(m+1)^4)
  have hmin : min k m ≤ m := min_le_right _ _
  have hb : s ≤ 1000*(m+1)^4 := by dsimp [s]; nlinarith [Nat.zero_le (m^4),Nat.zero_le (m^3),Nat.zero_le (m^2)]
  have hN : 1 ≤ N := visitsCount_pos m k
  have hp := Nat.mul_le_mul_right (1000*(m+1)^4) hN
  dsimp [D]
  nlinarith only [hb,hp]
end BipHamCount.Deterministic

open scoped BigOperators
open BipHamCount.Deterministic
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ v : Fin m,
          ((smallTerms m A B v (kOf m)).run 0).1 = sigmaSmall A B v (kOf m) ∧
          (((smallTerms m A B v (kOf m)).run 0).2 : ℝ) ≤ 
            C * ((m : ℝ)+1)^c * Real.exp (m*Real.binEntropy alpha) *
              (3 : ℝ)^(alpha*m) := by
  obtain ⟨C,hC,c,h⟩ := lemma_4_4
  refine ⟨C+4001,by linarith,c+4,?_⟩
  intro m A B hA hB v
  let k := kOf m
  have hk : k ≤ m := by dsimp [k,kOf]; omega
  let M : ℝ := m+1
  let t := ⌈C*M^c⌉₊
  have hyp := h m A B hA hB v k hk
  have val (X Y s) : ((computeF m A B v k X Y).run s).1 = Fval A B v k X Y := by
    rw [WorkCalc.eval (computeF_fixed m A B v k X Y) s]; exact (hyp X Y).1
  have tim (X Y s) : ((computeF m A B v k X Y).run s).2 ≤ s+t := by
    rw [WorkCalc.eval (computeF_fixed m A B v k X Y) s]
    exact Nat.add_le_add_left (Nat.cast_le.mp ((hyp X Y).2.trans (Nat.le_ceil _))) s
  refine ⟨(smallTerms_correct_from_F m A B v k 0 val).trans (lemma_4_3 m A B v k).symm,?_⟩
  let N := ∑ q ∈ Finset.range (k+1), m.choose q*3^q
  have ht := smallTerms_cost_F A B hA hB v k t val tim
  rw [min_eq_left hk] at ht
  have hcost : (((smallTerms m A B v k).run 0).2 : ℝ) ≤ (N:ℝ)*((t:ℝ)+4000*M^4) := by
    dsimp [N,M]; exact_mod_cast ht
  have hcount : (N:ℝ) ≤ Real.exp (m*Real.binEntropy alpha)*(3:ℝ)^(alpha*m) := by
    dsimp [N,k]; push_cast; exact smallTerms_index_enumeration.2.2 m
  have hM : 1 ≤ M := by dsimp [M]; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hcap : (t:ℝ) ≤ C*M^c+1 := (Nat.ceil_lt_add_one (show 0 ≤ C*M^c by positivity)).le
  have he1 : M^c ≤ M^(c+4) := pow_le_pow_right₀ hM (by omega)
  have he2 : M^4 ≤ M^(c+4) := pow_le_pow_right₀ hM (by omega)
  have he3 : (1:ℝ) ≤ M^(c+4) := one_le_pow₀ hM
  have cap : (t:ℝ)+4000*M^4 ≤ (C+4001)*M^(c+4) := by
    nlinarith only [hcap,mul_le_mul_of_nonneg_left he1 hC.le,he2,he3]
  calc
    _ ≤ (N:ℝ)*((t:ℝ)+4000*M^4) := hcost
    _ ≤ (Real.exp (m*Real.binEntropy alpha)*(3:ℝ)^(alpha*m))*((C+4001)*M^(c+4)) :=
      mul_le_mul hcount cap (by positivity) (by positivity)
    _ = _ := by dsimp [M]; ring
