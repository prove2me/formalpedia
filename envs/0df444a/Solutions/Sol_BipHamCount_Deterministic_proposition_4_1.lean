-- Prove2me | solution 1 for BipHamCount.Deterministic.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T11:04:48.295397+00:00
-- url     : https://prove2.me/submissions/3410536d-8e46-43a6-8e9c-df71f02533b6

import Definitions.Def_BipHamCount_Deterministic_Programs
import Definitions.Def_BipHamCount_Deterministic_Core
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.List.Sort
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Size
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds
import Theorems.Thm_BipHamCount_Deterministic_largeSummand_spec
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.Interval.Finset.Fin
import Theorems.Thm_BipHamCount_Deterministic_largeTerms_layer_enumeration
import Mathlib.Data.Nat.Choose.Bounds

section
open BipHamCount.Deterministic CapacitatedAssort.General
namespace CountLayers
abbrev Table := Array (ℤ × ℤ)
abbrev Pair := ℤ × ℤ
abbrev StepState := ℤ × Table
abbrev LayerState := Table × ℕ × ℤ

def cell {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (binom : Array (Array ℕ))
    (k q prevWidth : ℕ) (prev : Table) (I J : Finset (Fin m)) (first : Option (Fin m)) : Work Pair := do
  let mut pa : ℤ := 0
  let mut pb : ℤ := 0
  if q = 0 then
    pa := 1
    pb := 1
  else if let some i := first then
    charge (m+1)
    let Ip := I.erase i
    let rIp ← colex binom (k-(q-1)) Ip
    charge (8*(m+1)^3)
    for j in (J.sort (· ≤ ·)) do
      charge (m+5)
      let Jp := J.erase j
      let rJp ← colex binom 0 Jp
      let old ← tableRead m prevWidth rIp rJp prev
      let a ← zmul (A i j) old.1
      let b ← zmul (B j i) old.2
      pa ← zadd pa a
      pb ← zadd pb b
  return (pa,pb)

def entryStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (binom : Array (Array ℕ))
    (k q prevWidth nc ri : ℕ) (prev : Table) (I : Finset (Fin m)) (first : Option (Fin m))
    (J : Finset (Fin m)) (st : StepState) : Work (ForInStep StepState) := do
  let mut total := st.1
  let mut cur := st.2
  charge (4*(m+1))
  let rj ← colex binom 0 J
  let mut pa : ℤ := 0
  let mut pb : ℤ := 0
  if q = 0 then
    pa := 1
    pb := 1
  else if let some i := first then
    charge (m+1)
    let Ip := I.erase i
    let rIp ← colex binom (k-(q-1)) Ip
    charge (8*(m+1)^3)
    for j in (J.sort (· ≤ ·)) do
      charge (m+5)
      let Jp := J.erase j
      let rJp ← colex binom 0 Jp
      let old ← tableRead m prevWidth rIp rJp prev
      let a ← zmul (A i j) old.1
      let b ← zmul (B j i) old.2
      pa ← zadd pa a
      pb ← zadd pb b
  charge ((m+1)^2 + 8*(m+1)^3)
  cur := cur.set! (ri*nc+rj) (pa,pb)
  charge (2*(m+1))
  if k < q ∧ v ∉ I then
    let z ← largeSummand A B I J pa pb
    total ← zadd total z
  return .yield (total,cur)

def rowStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (binom : Array (Array ℕ))
    (k q prevWidth nc : ℕ) (prev : Table) (cols : List (Finset (Fin m)))
    (I : Finset (Fin m)) (st : StepState) : Work (ForInStep StepState) := do
  charge (8*(m+1)^3)
  let ri ← colex binom (k-q) I
  let s ← forIn cols st (entryStep A B v binom k q prevWidth nc ri prev I (I.sort (· ≤ ·)).head?)
  return .yield s

def layerStep {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (binom : Array (Array ℕ))
    (all : List (Fin m)) (k q : ℕ) (st : LayerState) : Work (ForInStep LayerState) := do
  let prev := st.1
  let prevWidth := st.2.1
  let total := st.2.2
  charge (8*(m+1)^3)
  let lo := k-q
  let rowUniverse ← suffix (m := m) lo
  let rows ← chooseSets rowUniverse q
  let cols ← chooseSets all q
  let nr := ((binom[m-lo]?.getD #[])[q]?.getD 0)
  let nc := ((binom[m]?.getD #[])[q]?.getD 0)
  charge ((nr*nc+1)*((m+1)^2+1))
  let start := (total,Array.replicate (nr*nc) ((0:ℤ),(0:ℤ)))
  let s ← forIn rows start (rowStep A B v binom k q prevWidth nc prev cols)
  return .yield (s.2,nc,s.1)

def work {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) : Work ℤ := do
  let binom ← binomTable m
  let all ← suffix (m:=m) 0
  charge (4*(m+1)+1)
  let s ← forIn (List.range (m+1)) ((#[],0,0) : LayerState) (layerStep A B v binom all k)
  return s.2.2

theorem factor {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    largeTerms m A B v k = work A B v k := by rfl
end CountLayers

end

section

namespace LargeDP
open BipHamCount.Deterministic Finset Matrix
open scoped BigOperators
theorem permMinor_natAbs {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (I J : Finset (Fin m)) : (permMinor A I J).natAbs ≤ m.factorial := by
  classical
  rw [permMinor]
  split
  next hc =>
    unfold Matrix.permanent
    apply (Int.natAbs_sum_le _ _).trans
    calc _ ≤ ∑ _ : Equiv.Perm (Fin I.card), (1 : ℕ) := Finset.sum_le_sum fun π _ => by
          change Int.natAbsHom (∏ i, squareSub A I J hc (π i) i) ≤ 1
          rw [map_prod]
          apply le_trans (Finset.prod_le_prod' (g := fun _ => (1 : ℕ)) ?_) (by simp)
          intro i _
          change (A (I.orderEmbOfFin rfl (π i)) (J.orderEmbOfFin hc i)).natAbs ≤ 1
          rcases hA (I.orderEmbOfFin rfl (π i)) (J.orderEmbOfFin hc i) with h|h <;> simp [h]
         _ ≤ _ := by simpa [Fintype.card_perm] using Nat.factorial_le (show I.card ≤ m by simpa using card_le_univ I)
  next _ => simp

theorem permMinor_power {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (I J : Finset (Fin m)) : (permMinor A I J).natAbs ≤ 2^(m*m) := by
  apply (permMinor_natAbs A hA I J).trans
  calc m.factorial ≤ m^m := Nat.factorial_le_pow _
       _ ≤ (2^m)^m := Nat.pow_le_pow_left Nat.lt_two_pow_self.le m
       _ = _ := (pow_mul ..).symm

end LargeDP

end

section

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LargeDP
open BipHamCount.Deterministic Matrix Finset
open scoped BigOperators Matrix

private lemma rect_remap {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (M : Matrix I J ℤ) (e : I' ≃ I) (f : J' ≃ J) :
    rectPermanent (M.submatrix e f) = rectPermanent M := by
  classical
  unfold rectPermanent
  rw [← (e.equivCongr f).sum_comp]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← e.prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp [Equiv.equivCongr, Matrix.submatrix_apply]

private lemma rect_option {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] (M : Matrix (Option I) J ℤ) :
    rectPermanent M = ∑ j : J, M none j * rectPermanent (fun (i : I) (y : {x : J // x ≠ j}) => M (some i) y) := by
  classical
  let b : (Σ j : J, I ≃ {z : J // z ≠ j}) ≃ (Option I ≃ J) :=
    (Equiv.sigmaCongrRight (fun j => (Equiv.optionSubtype j).symm)).trans
      (Equiv.sigmaFiberEquiv (fun e : Option I ≃ J => e none))
  unfold rectPermanent
  calc
    _ = ∑ r : (Σ j : J, I ≃ {z : J // z ≠ j}), ∏ i, M i ((b r) i) := by
      convert (b.sum_comp (fun e : Option I ≃ J => ∏ i, M i (e i))).symm using 1 <;> congr 1 <;> ext z <;> simp
    _ = _ := by
      rw [Fintype.sum_sigma]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_sum]
      refine sum_congr (by ext z; simp) fun p _ => ?_
      rw [Fintype.prod_option]
      rfl

private lemma perm_rect {I : Type*} [Fintype I] [DecidableEq I] (M : Matrix I I ℤ) :
    M.permanent = rectPermanent M := by
  rw [← Matrix.permanent_transpose]
  classical
  unfold Matrix.permanent rectPermanent
  congr 1
  ext π; simp

private lemma sub_rect {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m)) (h : T.card = S.card) :
    permMinor A S T = rectPermanent (A.submatrix Subtype.val Subtype.val : Matrix S T ℤ) := by
  rw [permMinor,dif_pos h,perm_rect]
  exact rect_remap (A.submatrix Subtype.val Subtype.val : Matrix S T ℤ) (S.orderIsoOfFin rfl).toEquiv (T.orderIsoOfFin h).toEquiv

private def eraseEquiv {m : ℕ} (S : Finset (Fin m)) (i : S) : (S.erase i.1) ≃ {x : S // x ≠ i} where
  toFun j := ⟨⟨j.1,(mem_erase.mp j.2).2⟩,fun h => (mem_erase.mp j.2).1 (congrArg Subtype.val h)⟩
  invFun j := ⟨j.1.1,mem_erase.mpr ⟨fun h => j.2 (Subtype.ext h),j.1.2⟩⟩
  left_inv j := by rfl
  right_inv j := by rfl

private lemma erase_rect {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m))
    (i : S) (j : T) (h : T.card = S.card) :
    rectPermanent (fun (x : S.erase i.1) (y : {x : T // x ≠ j}) => A x.1 y.1.1) =
      permMinor A (S.erase i.1) (T.erase j.1) := by
  have hc : (T.erase j.1).card = (S.erase i.1).card := by simp [card_erase_of_mem i.2,card_erase_of_mem j.2,h]
  rw [sub_rect A _ _ hc]
  symm
  exact rect_remap (fun (x : S.erase i.1) (y : {x : T // x ≠ j}) => A x.1 y.1.1) (Equiv.refl _) (eraseEquiv T j)

theorem permMinor_laplace {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (S T : Finset (Fin m)) (h : T.card=S.card) (i : Fin m) (hi : i ∈ S) :
    permMinor A S T = ∑ j ∈ T, A i j * permMinor A (S.erase i) (T.erase j) := by
  classical
  let i' : S := ⟨i,hi⟩
  let e : Option (S.erase i) ≃ S := (eraseEquiv S i').optionCongr.trans (Equiv.optionSubtypeNe i')
  let M : Matrix S T ℤ := A.submatrix Subtype.val Subtype.val
  rw [sub_rect A S T h]
  change rectPermanent M = _
  rw [← rect_remap M e (Equiv.refl T), rect_option,← Finset.sum_coe_sort T]
  refine sum_congr rfl fun j _ => ?_
  change A i j * rectPermanent (fun (x : S.erase i) (y : {x : T // x ≠ j}) => A x.1 y.1.1) = _
  rw [erase_rect A S T i' j h]

theorem permMinor_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m))
    (h : T.card=S.card) : permMinor Aᵀ S T = permMinor A T S := by
  classical
  rw [sub_rect _ _ _ h, sub_rect _ _ _ h.symm]
  let e : (S ≃ T) ≃ (T ≃ S) := ⟨Equiv.symm,Equiv.symm,fun _ => rfl,fun _ => rfl⟩
  unfold rectPermanent
  calc
    _ = ∑ p : S ≃ T, ∏ j : T, A j (p.symm j) := by
      refine Finset.sum_congr (by ext; simp) fun p _ => ?_
      change (∏ i : S, A (p i) i) = ∏ j : T, A j (p.symm j)
      rw [← p.prod_comp (fun j : T => A j (p.symm j))]
      simp
    _ = _ := by
      convert e.sum_comp (fun p : T ≃ S => ∏ j : T, A j (p j)) using 1 <;> congr 1 <;> ext z <;> simp

end LargeDP

end

section
open BipHamCount.Deterministic CapacitatedAssort.General
namespace ColexBounds

def rank : List ℕ → ℕ
  | [] => 0
  | i :: xs => i.choose (xs.length+1) + rank xs

theorem rank_lt {m : ℕ} (xs : List ℕ) (hd : xs.Pairwise (· > ·)) (hm : ∀ i∈xs, i < m) :
    rank xs < m.choose xs.length := by
  induction xs generalizing m with
  | nil => simp [rank]
  | cons i xs ih =>
    obtain ⟨hlt,hrs⟩ := List.pairwise_cons.mp hd
    have hi : i < m := hm _ (by simp)
    have h1 := ih hrs hlt
    have h2 := Nat.choose_le_choose (xs.length+1) (show i+1 ≤ m by omega)
    simp only [rank,List.length_cons, Nat.choose_succ_succ,Nat.succ_eq_add_one] at *
    omega

theorem rank_inj (xs ys : List ℕ) (hx : xs.Pairwise (· > ·)) (hy : ys.Pairwise (· > ·))
    (hlen : xs.length=ys.length) (he : rank xs=rank ys) : xs=ys := by
  induction xs generalizing ys with
  | nil => simpa using hlen.symm
  | cons i xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons j ys =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      have hx' := List.pairwise_cons.mp hx
      have hy' := List.pairwise_cons.mp hy
      have hij : i=j := by
        by_contra hn
        rcases lt_or_gt_of_ne hn with h | h
        · have hr := rank_lt (m:=j) (i::xs) hx (by
            intro a ha; rcases List.mem_cons.mp ha with rfl|ha
            · exact h
            · exact (hx'.1 a ha).trans h)
          simp only [List.length_cons,hlen] at hr
          rw [he,rank] at hr; omega
        · have hr := rank_lt (m:=i) (j::ys) hy (by
            intro a ha; rcases List.mem_cons.mp ha with rfl|ha
            · exact h
            · exact (hy'.1 a ha).trans h)
          simp only [List.length_cons,←hlen] at hr
          rw [←he,rank] at hr; omega
      subst j
      exact congrArg (List.cons i) (ih ys hx'.2 hy'.2 hlen (by simpa [rank,hlen] using he))
end ColexBounds

end

section
open BipHamCount.Deterministic CapacitatedAssort.General
namespace ColexBounds
private def rankFrom (f : ℕ → ℕ → ℕ) (t : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => f x t + rankFrom f (t+1) xs

private theorem rankFrom_append (f : ℕ → ℕ → ℕ) (t : ℕ) (xs ys : List ℕ) :
    rankFrom f t (xs++ys)=rankFrom f t xs+rankFrom f (t+xs.length) ys := by
  induction xs generalizing t with
  | nil => simp [rankFrom]
  | cons x xs ih => simp [rankFrom,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem rank_rev (xs : List ℕ) : rankFrom Nat.choose 1 xs=rank xs.reverse := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp [rankFrom_append,rankFrom,rank,ih,Nat.add_comm]

private def colexGo {m} (binom : Array (Array ℕ)) (lo : ℕ) (xs : List (Fin m)) (r t : ℕ) : Work ℕ := do
  let mut rank := r
  let mut t := t
  for i in xs do
    charge (8*(m+1)^2)
    rank := rank + ((binom[i.val-lo]?.getD #[])[t]?.getD 0)
    t := t+1
  return rank

private theorem colexGo_spec {m} (b : Array (Array ℕ)) (lo : ℕ) (xs : List (Fin m)) (r t s : ℕ)
    (h : ∀ i∈xs, ∀ j, t ≤ j → j < t+xs.length → ((b[i.val-lo]?.getD #[])[j]?.getD 0)=(i.val-lo).choose j) :
    (colexGo b lo xs r t).run s = (r+rankFrom Nat.choose t (xs.map (fun i => i.val-lo)), s+xs.length*(8*(m+1)^2)) := by
  induction xs generalizing r t s with
  | nil => simp [colexGo,rankFrom]; rfl
  | cons x xs ih =>
    let i := x.val-lo
    have hx : ((b[x.val-lo]?.getD #[])[t]?.getD 0)=i.choose t := h x (by simp) _ (by omega) (by simp)
    have eqn : (colexGo b lo (x::xs) r t).run s =
        (colexGo b lo xs (r+i.choose t) (t+1)).run (s+8*(m+1)^2) := by
      simp [colexGo,charge,StateT.run_bind,hx]
    rw [eqn,ih]
    · simp [rankFrom,i,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · intro y hy j hj hj'
      exact h _ (by simp [hy]) _ (by omega) (by simp only [List.length_cons]; omega)

theorem colex_spec {m : ℕ} (b : Array (Array ℕ)) (lo s : ℕ) (U : Finset (Fin m))
    (h : ∀ i j, i < m → j ≤ m → ((b[i]?.getD #[])[j]?.getD 0)=i.choose j) :
    (colex b lo U).run s =
      (rank (((U.sort (· ≤ ·)).map (fun i => i.val-lo)).reverse),s+8*(m+1)^3+U.card*(8*(m+1)^2)) := by
  let xs := U.sort (· ≤ ·)
  have hx : xs.length=U.card := by simp [xs]
  have hc : U.card ≤ m := by simpa using Finset.card_le_univ U
  change (colexGo b lo xs 0 1).run (s+8*(m+1)^3)=_
  rw [colexGo_spec,rank_rev,zero_add,hx]
  intro i _ j _ hj
  exact h _ _ (by have := i.isLt; omega) (by omega)
end ColexBounds

end

section

namespace BerkowitzModel

open CapacitatedAssort.General BipHamCount.Deterministic Finset
open scoped BigOperators

structure Post {α : Type} (p : Work α) (Q : α → Prop) : Prop where
  run : ∀ s, Q ((p.run s).1)
def Yield {α : Type} (Q : α → Prop) : ForInStep α → Prop
  | .yield x => Q x
  | .done _ => False

theorem purePost {α : Type} {Q : α → Prop} {x : α} (h : Q x) : Post (pure x) Q := ⟨fun _ => h⟩

theorem bindPost {α β : Type} {p : Work α} {f : α → Work β} {Q : α → Prop} {S : β → Prop}
    (hp : Post p Q) (hf : ∀ x, Q x → Post (f x) S) : Post (p >>= f) S :=
  ⟨fun s => (hf _ (hp.run s)).run _⟩

theorem tickPost {α : Type} {k : ℕ} {p : Work α} {Q : α → Prop} (hp : Post p Q) :
    Post (charge k >>= fun _ => p) Q := ⟨fun s => hp.run (s+k)⟩

theorem postMono {α : Type} {p : Work α} {Q S : α → Prop} (hp : Post p Q) (h : ∀ x, Q x → S x) :
    Post p S := ⟨fun s => h _ (hp.run s)⟩

theorem rangePost {α : Type} {n : ℕ} {p : ℕ → α → Work (ForInStep α)} {b : α}
    (I : ℕ → α → Prop) (h0 : I 0 b)
    (step : ∀ k < n, ∀ a, I k a → Post (p k a) (Yield (I (k+1)))) :
    Post (forIn (List.range n) b p) (I n) := by
  have aux (t len : ℕ) (a : α) (ht : t+len = n) (ha : I t a) :
      Post (forIn (List.range' t len) a p) (I n) := by
    induction len generalizing t a with
    | zero =>
      simp only [List.range'_zero,List.forIn_nil]
      exact purePost (by simpa using ht ▸ ha)
    | succ len ih =>
      rw [List.range'_succ,List.forIn_cons]
      apply bindPost (step t (by omega) a ha)
      intro z hz
      cases z with
      | done y => exact False.elim hz
      | yield y => exact ih _ _ (by omega) hz
  simpa only [List.range_eq_range'] using aux 0 n b (by omega) h0

structure RingModel {R K : Type} [CommRing K] (O : RingOps R) (v : R → K) : Prop where
  zero : v O.zero = 0
  one : v O.one = 1
  add (x y) : Post (O.add x y) (fun z => v z = v x + v y)
  mul (x y) : Post (O.mul x y) (fun z => v z = v x * v y)
  neg (x) : Post (O.neg x) (fun z => v z = -v x)

variable {R K : Type} [CommRing K] {O : RingOps R} {v : R → K}

structure Prefix (O : RingOps R) (v : R → K) (a : Array R) (n : ℕ) (f : ℕ → K) : Prop where
  size : a.size = n
  atLt : ∀ i < n, v (a[i]?.getD O.zero) = f i

omit [CommRing K] in
theorem prefixEmpty (f : ℕ → K) : Prefix O v #[] 0 f :=
  ⟨rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩

theorem prefixPush {a : Array R} {n : ℕ} {f : ℕ → K} (ha : Prefix O v a n f) {x : R} (hx : v x = f n) :
    Prefix O v (a.push x) (n+1) f := by
  refine ⟨by simp [ha.size],?_⟩
  intro i hi
  by_cases h : i < n
  · rw [Array.getElem?_push_lt (ha.size ▸ h)]
    simpa [Array.getElem?_eq_getElem (ha.size ▸ h)] using ha.atLt i h
  · have : i = n := by omega
    rw [Array.getElem?_push,ha.size,if_pos this]
    simpa [this] using hx

theorem arrayLoop {n : ℕ} {f : ℕ → K} {p : ℕ → Array R → Work (ForInStep (Array R))}
    (hs : ∀ k < n, ∀ a, Prefix O v a k f →
      Post (p k a) (Yield (fun b => Prefix O v b (k+1) f))) :
    Post (forIn (List.range n) #[] p) (fun b => Prefix O v b n f) :=
  rangePost (fun k a => Prefix O v a k f) (prefixEmpty _) hs

theorem sumLoop {n : ℕ} {f : ℕ → K} (model : RingModel O v) {p : ℕ → R → Work (ForInStep R)}
    (hs : ∀ k < n, ∀ a, Post (p k a) (Yield (fun z => v z = v a + f k))) :
    Post (forIn (List.range n) O.zero p) (fun a => v a = ∑ i ∈ range n, f i) := by
  apply rangePost (fun k a => v a = ∑ i ∈ range k, f i)
  · simpa using model.zero
  · intro k hk a ha
    apply postMono (hs k hk a)
    intro z hz
    cases z with
    | done _ => exact hz
    | yield z => simpa [Yield,Finset.sum_range_succ,← ha] using hz

end BerkowitzModel

end

section
namespace BerkowitzModel
open CapacitatedAssort.General

structure Budget {α : Type} (p : Work α) (Q : α → Prop) (c : ℕ) : Prop where
  run : ∀ s, Q ((p.run s).1) ∧ (p.run s).2 ≤ s+c

theorem bPure {α : Type} {x : α} {Q : α → Prop} (h : Q x) : Budget (pure x) Q 0 :=
  ⟨fun s => ⟨h,Nat.le_refl _⟩⟩

theorem bBind {α β : Type} {p : Work α} {Q : α → Prop} {f : α → Work β} {S : β → Prop} {u w : ℕ}
    (hp : Budget p Q u) (hf : ∀ x, Q x → Budget (f x) S w) : Budget (p >>= f) S (u+w) := by
  constructor
  intro s
  obtain ⟨hp, hc⟩ := hp.run s
  obtain ⟨hy, hd⟩ := (hf _ hp).run (p.run s).2
  exact ⟨hy,by change ((f (p.run s).1).run (p.run s).2).2 ≤ _; omega⟩

theorem bTick {α : Type} {p : Work α} {Q : α → Prop} {k c : ℕ}
    (h : Budget p Q c) : Budget (charge k >>= fun _ => p) Q (k+c) := by
  constructor
  intro s
  change Q (p.run (s+k)).1 ∧ (p.run (s+k)).2 ≤ s+(k+c)
  simpa only [Nat.add_assoc] using h.run (s+k)

theorem bWeaken {α : Type} {p : Work α} {Q Q' : α → Prop} {c c' : ℕ}
    (h : Budget p Q c) (q : ∀ x, Q x → Q' x) (hc : c ≤ c') : Budget p Q' c' := by
  constructor; intro s
  exact ⟨q _ (h.run s).1,(h.run s).2.trans (by omega)⟩

theorem bLe {α : Type} {p : Work α} {Q : α → Prop} {c c' : ℕ}
    (h : Budget p Q c) (hc : c ≤ c') : Budget p Q c' := bWeaken h (fun _ => id) hc

theorem bMap {α : Type} {p : Work α} {Q Q' : α → Prop} {c : ℕ}
    (h : Budget p Q c) (q : ∀ x, Q x → Q' x) : Budget p Q' c := bWeaken h q le_rfl

theorem bValue {α : Type} {p : Work α} {Q S : α → Prop} {c : ℕ}
    (h : Budget p Q c) (v : Post p S) : Budget p (fun x => Q x ∧ S x) c :=
  ⟨fun s => ⟨⟨(h.run s).1,v.run s⟩,(h.run s).2⟩⟩

theorem bRange {α : Type} {n c : ℕ} {p : ℕ → α → Work (ForInStep α)} {b : α}
    (I : ℕ → α → Prop) (hb : I 0 b)
    (step : ∀ k < n, ∀ a, I k a → Budget (p k a) (Yield (I (k+1))) c) :
    Budget (forIn (List.range n) b p) (I n) (n*c) := by
  have aux (t len : ℕ) (a : α) (ht : t+len=n) (ha : I t a) :
      Budget (forIn (List.range' t len) a p) (I n) (len*c) := by
    induction len generalizing t a with
    | zero => simp only [List.range'_zero,List.forIn_nil,Nat.zero_mul]; exact bPure (by simpa using ht ▸ ha)
    | succ len ih =>
      rw [List.range'_succ,List.forIn_cons,Nat.succ_mul,Nat.add_comm (len*c) c]
      apply bBind (step t (by omega) a ha)
      intro z hz
      cases z with
      | done _ => exact False.elim hz
      | yield y => exact ih _ _ (by omega) hz
  simpa only [List.range_eq_range'] using aux 0 n b (by omega) hb

theorem bList {α β : Type} {c : ℕ} {p : α → β → Work (ForInStep β)} (L : List α)
    (I : β → Prop) (b : β) (hb : I b) (step : ∀ i ∈ L, ∀ a, I a → Budget (p i a) (Yield I) c) :
    Budget (forIn L b p) I (L.length*c) := by
  induction L generalizing b with
  | nil => simp only [List.forIn_nil,List.length_nil,Nat.zero_mul]; exact bPure hb
  | cons i xs ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*c) c]
    apply bBind (step i (by simp) b hb)
    intro z hz
    cases z with
    | done _ => exact False.elim hz
    | yield y => exact ih y hz (fun j hj => step j (by simp [hj]))

end BerkowitzModel

end

section

namespace LargeDP
open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel Finset
open scoped BigOperators Matrix

def key {m : ℕ} (lo : ℕ) (I : Finset (Fin m)) : ℕ :=
  ColexBounds.rank (((I.sort (· ≤ ·)).map (fun i => i.val-lo)).reverse)
noncomputable def pair {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (I J : Finset (Fin m)) : ℤ × ℤ :=
  (permMinor A I J,permMinor B J I)
def widthLimit (m : ℕ) := m*m+m+2
def arithmeticCost (m : ℕ) := (2*widthLimit m+3)^2
def addressCost (m : ℕ) := 8*(m+1)^3 + m*(8*(m+1)^2)
def readCost (m : ℕ) := (m+1)^2+8*(m+1)^3
def colStepCost (m : ℕ) := (m+5)+addressCost m+readCost m+4*arithmeticCost m
def cellCost (m : ℕ) := (m+1)+addressCost m+8*(m+1)^3+m*colStepCost m

theorem rankBudget {m : ℕ} (binom : Array (Array ℕ)) (lo : ℕ) (I : Finset (Fin m))
    (h : ∀ r j, r < m → j ≤ m → ((binom[r]?.getD #[])[j]?.getD 0)=r.choose j) :
    Budget (colex binom lo I) (· = key lo I) (addressCost m) := by
  constructor; intro s
  rw [ColexBounds.colex_spec binom lo s I h]
  refine ⟨rfl,?_⟩
  have hi : I.card ≤ m := by simpa using card_le_univ I
  unfold addressCost
  simpa [Nat.add_assoc] using hi

private lemma arith (m : ℕ) (f : ℤ → ℤ → Work ℤ) (v : ℤ → ℤ → ℤ) (x y : ℤ)
    (hh : ∀ s, (f x y).run s=(v x y,s+(x.natAbs.size+y.natAbs.size+1)^2))
    (hx : x.natAbs ≤ 2^(widthLimit m)) (hy : y.natAbs ≤ 2^(widthLimit m)) :
    Budget (f x y) (· = v x y) (arithmeticCost m) := by
  constructor; intro s; rw [hh]
  refine ⟨rfl,Nat.add_le_add_left ?_ s⟩
  have hsize (q b : ℕ) (h : q ≤ 2^b) : q.size ≤ b+1 :=
    Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos b; omega))
  unfold arithmeticCost
  exact Nat.pow_le_pow_left (by have := hsize _ _ hx; have := hsize _ _ hy; omega) _

private lemma pairFold {α : Type} (L : List α) (f g : α → ℤ)
    (p : α → (ℤ × ℤ) → Work (ForInStep (ℤ × ℤ))) (m Q t : ℕ)
    (hl : ∀ i ∈ L, (f i).natAbs ≤ Q ∧ (g i).natAbs ≤ Q)
    (hb : ∀ i ∈ L, ∀ a b : ℤ, a.natAbs ≤ m*Q → b.natAbs ≤ m*Q →
      Budget (p i (a,b)) (· = .yield (a+f i,b+g i)) t)
    (a b : ℤ) (k : ℕ) (ha : a.natAbs ≤ k*Q) (hb' : b.natAbs ≤ k*Q) (hk : k+L.length ≤ m) :
    Budget (forIn L (a,b) p) (· = (a+(L.map f).sum,b+(L.map g).sum)) (L.length*t) := by
  induction L generalizing a b k with
  | nil => simp only [List.forIn_nil,List.length_nil,Nat.zero_mul,List.map_nil,List.sum_nil,add_zero]; apply bPure; rfl
  | cons x xs ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*t) _]
    have hm := Nat.mul_le_mul_right Q (show k ≤ m by omega)
    apply bBind (hb x (by simp) a b (ha.trans hm) (hb'.trans hm))
    intro val hv; subst val
    have hx := hl x (by simp)
    have hx1 : (a+f x).natAbs ≤ (k+1)*Q := by rw [Nat.add_mul,one_mul]; exact (Int.natAbs_add_le ..).trans (Nat.add_le_add ha hx.1)
    have hx2 : (b+g x).natAbs ≤ (k+1)*Q := by rw [Nat.add_mul,one_mul]; exact (Int.natAbs_add_le ..).trans (Nat.add_le_add hb' hx.2)
    apply bMap (ih (fun z hz => hl z (by simp [hz])) (fun z hz => hb z (by simp [hz]))
      _ _ (k+1) hx1 hx2 (by simp at hk; omega))
    intro r hr; simpa [add_assoc] using hr

def colBody {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (binom : Array (Array ℕ)) (prev : Array (ℤ × ℤ))
    (prevWidth ri : ℕ) (i : Fin m) (J : Finset (Fin m)) (j : Fin m) (p : ℤ × ℤ) :
    Work (ForInStep (ℤ × ℤ)) := do
  charge (m+5)
  let rj ← colex binom 0 (J.erase j)
  let old ← tableRead m prevWidth ri rj prev
  let a ← zmul (A i j) old.1
  let b ← zmul (B j i) old.2
  let a ← zadd p.1 a
  let b ← zadd p.2 b
  return .yield (a,b)

def evalCell {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (binom : Array (Array ℕ)) (prev : Array (ℤ × ℤ))
    (prevWidth k q : ℕ) (I J : Finset (Fin m)) (first : Option (Fin m)) : Work (ℤ × ℤ) := do
  if q=0 then return (1,1)
  else if let some i := first then
    charge (m+1)
    let ri ← colex binom (k-(q-1)) (I.erase i)
    charge (8*(m+1)^3)
    forIn (J.sort (· ≤ ·)) (0,0) (colBody A B binom prev prevWidth ri i J)
  else return (0,0)

theorem colFoldBudget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (binom : Array (Array ℕ)) (ht : ∀ r j, r < m → j ≤ m → ((binom[r]?.getD #[])[j]?.getD 0)=r.choose j)
    (prev : Array (ℤ × ℤ)) (w ri : ℕ) (i : Fin m) (I J : Finset (Fin m)) (hi : i∈I) (hc : J.card=I.card)
    (hold : ∀ j∈J, prev[ri*w+key 0 (J.erase j)]?.getD (0,0)=pair A B (I.erase i) (J.erase j)) :
    Budget (forIn (J.sort (· ≤ ·)) (0,0) (colBody A B binom prev w ri i J))
      (· = pair A B I J) (m*colStepCost m) := by
  let f := fun j => A i j * permMinor A (I.erase i) (J.erase j)
  let g := fun j => B j i * permMinor B (J.erase j) (I.erase i)
  let Q := 2^(m*m)
  let G := widthLimit m
  have hadd : m*Q ≤ 2^G := calc
    _ ≤ 2^m*2^(m*m) := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _ ≤ _ := by rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); unfold G widthLimit; omega
  have hQ : Q ≤ 2^G := Nat.pow_le_pow_right (by decide) (by dsimp [G,widthLimit]; omega)
  have hOne : (1 : ℕ) ≤ 2^G := one_le_pow₀ (by decide)
  have bound (j : Fin m) : (f j).natAbs ≤ Q ∧ (g j).natAbs ≤ Q := by
    constructor
    · rcases hA i j with h|h <;> simp [f,h]; exact permMinor_power A hA _ _
    · rcases hB j i with h|h <;> simp [g,h]; exact permMinor_power B hB _ _
  have step (j : Fin m) (hj : j∈J) (a b : ℤ) (ha : a.natAbs ≤ m*Q) (hb : b.natAbs ≤ m*Q) :
      Budget (colBody A B binom prev w ri i J j (a,b)) (· = .yield (a+f j,b+g j)) (colStepCost m) := by
    have hlookup : Budget (tableRead m w ri (key 0 (J.erase j)) prev) (· = pair A B (I.erase i) (J.erase j)) (readCost m) :=
      ⟨fun _ => ⟨hold j hj,le_rfl⟩⟩
    have hA1 : (A i j).natAbs ≤ 2^G := by rcases hA i j with h|h <;> simp [h,hOne]
    have hB1 : (B j i).natAbs ≤ 2^G := by rcases hB j i with h|h <;> simp [h,hOne]
    let z := arithmeticCost m
    rw [colBody]
    refine bLe (bTick (bBind (w := readCost m+4*z) (rankBudget binom 0 (J.erase j) ht) ?_)) (by dsimp [colStepCost,z]; omega)
    intro r hr; subst r
    apply bBind hlookup
    intro o ho; subst o
    refine bLe (bBind (w := 3*z) (arith m zmul (·*·) _ _ (fun _ => rfl) hA1 ((permMinor_power A hA _ _).trans hQ)) ?_) (by dsimp [z]; omega)
    intro x hx
    refine bLe (bBind (w := 2*z) (arith m zmul (·*·) _ _ (fun _ => rfl) hB1 ((permMinor_power B hB _ _).trans hQ)) ?_) (by dsimp [z]; omega)
    intro y hy
    refine bLe (bBind (w := z) (arith m zadd (·+·) _ x (fun _ => rfl) (ha.trans hadd) (hx ▸ (bound j).1.trans hQ)) ?_) (by dsimp [z]; omega)
    intro x' hx'
    refine bLe (bBind (w := 0) (arith m zadd (·+·) _ y (fun _ => rfl) (hb.trans hadd) (hy ▸ (bound j).2.trans hQ)) ?_) (by dsimp [z]; omega)
    intro y' hy'
    apply bPure
    rw [hx',hy',hx,hy]; rfl
  have hlen : (J.sort (· ≤ ·)).length ≤ m := by simpa using card_le_univ J
  have hfold := pairFold (J.sort (· ≤ ·)) f g _ m Q (colStepCost m)
    (fun j _ => bound j) (fun j hj => step j (by simpa using hj)) 0 0 0 (by simp) (by simp) (by simpa using hlen)
  refine bWeaken hfold ?_ (Nat.mul_le_mul_right _ hlen)
  intro out hout
  have sl (f : Fin m → ℤ) : ((J.sort (· ≤ ·)).map f).sum = ∑ j ∈ J, f j :=
    ((J.sort_perm_toList (· ≤ ·)).map f).sum_eq.trans (J.sum_map_toList f)
  rw [hout,zero_add,zero_add,sl,sl,pair]
  congr 1
  · exact (permMinor_laplace A I J hc i hi).symm
  · rw [← permMinor_transpose B I J hc,permMinor_laplace Bᵀ I J hc i hi]
    refine sum_congr rfl fun j hj => ?_
    have hc' : (J.erase j).card = (I.erase i).card := by simp [card_erase_of_mem hi,card_erase_of_mem hj,hc]
    simp [g,permMinor_transpose B (I.erase i) (J.erase j) hc']

end LargeDP

end

section
open BipHamCount.Deterministic
namespace BerkowitzModel

def opCost (g : ℕ) : ℕ := 100*(g+2)^4
def polyFits (a : ZPoly) (u : ℕ) : Prop := a.size ≤ u ∧ ∀ i : ℕ, (a[i]?.getD 0).natAbs ≤ 2^u
def intFits (x : ℤ) (u : ℕ) := x.natAbs ≤ 2^u
def bufFits {R : Type} (O : RingOps R) (Fits : R → ℕ → Prop) (a : Array R) (u : ℕ) : Prop :=
  ∀ i : ℕ, Fits (a[i]?.getD O.zero) u
def matrixFits {R : Type} (O : RingOps R) (Fits : R → ℕ → Prop) (a : Array (Array R)) (u : ℕ) : Prop :=
  ∀ i : ℕ, bufFits O Fits (a[i]?.getD #[]) u
def vBound (d u l : ℕ) : ℕ := u+l*(2*u+d+4)
def tBound (d u : ℕ) : ℕ := vBound d u (d+1)
def cBound (d u n : ℕ) : ℕ := 1+n*(2*tBound d u+d+4)
def cap (d u : ℕ) : ℕ := cBound d u (d+1)+tBound d u+u+d+5
def basicTime (d u : ℕ) : ℕ := opCost (cap d u)+8*(d+3)+16
def layerTime1 (d u : ℕ) : ℕ := 16*(d+3)*basicTime d u
def layerTime2 (d u : ℕ) : ℕ := 16*(d+3)*layerTime1 d u
def layerTime3 (d u : ℕ) : ℕ := 16*(d+3)*layerTime2 d u
def coefficientTime (d u n : ℕ) : ℕ := (n+1)*(10*layerTime3 d u)
def determinantTime (n u : ℕ) := coefficientTime n u n+basicTime n u+basicTime n u

theorem uploaded_poly_determinant_budget (M : Array (Array ZPoly)) (n u : ℕ) (hu : 1 ≤ u)
    (hm : matrixFits polyOps polyFits M u) :
    Budget (berkowitz polyOps n M) (fun x => polyFits x (cBound n u n)) (determinantTime n u) :=
  ⟨fun s => (berkowitz_bit_bounds n u hu).2 M s hm⟩

theorem uploaded_integer_determinant_budget (M : Array (Array ℤ)) (n u : ℕ) (hu : 1 ≤ u)
    (hm : matrixFits intOps intFits M u) :
    Budget (berkowitz intOps n M) (fun x => intFits x (cBound n u n)) (determinantTime n u) :=
  ⟨fun s => (berkowitz_bit_bounds n u hu).1 M s hm⟩

end BerkowitzModel

end

section
open BipHamCount.Deterministic BerkowitzModel CapacitatedAssort.General Finset
namespace LargeSumm
def minorTime (m : ℕ) := 8*(m+1)^3+m*(2+m*3+1)
def outSize (m b : ℕ) : ℕ := 2*b+2*cBound m 1 m+1
def cost (m b : ℕ) : ℕ :=
  4*(m+1)+2*minorTime m+2*determinantTime m 1+(m+2)^2+4*(2*outSize m b+3)^2

theorem large_summand_budget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (S T : Finset (Fin m)) (hc : T.card = S.card) (pa pb : ℤ) (b : ℕ)
    (ha : pa.natAbs ≤ 2^b) (hb : pb.natAbs ≤ 2^b) :
    Budget (largeSummand A B S T pa pb) (fun out =>
      out = (-1 : ℤ)^(Sᶜ.card+1)*pa*pb*minor A Sᶜ Tᶜ*minor B Tᶜ Sᶜ ∧
      out.natAbs ≤ 2^(outSize m b)) (cost m b) := ⟨largeSummand_spec A B hA hB S T hc pa pb b ha hb⟩
end LargeSumm

end

section
namespace LargeDP
open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel Finset
open scoped BigOperators Matrix

theorem cell_budget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (binom : Array (Array ℕ)) (ht : ∀ r j, r < m → j ≤ m → ((binom[r]?.getD #[])[j]?.getD 0)=r.choose j)
    (prev : Array (ℤ × ℤ)) (w k q : ℕ) (I J : Finset (Fin m)) (hc : I.card=q) (hd : J.card=q)
    (hlow : ∀ x∈I, k-q ≤ x.val)
    (hold : 0 < q → ∀ I' J' : Finset (Fin m), I'.card=q-1 → J'.card=q-1 → (∀ x∈I', k-(q-1) ≤ x.val) →
      prev[key (k-(q-1)) I'*w+key 0 J']?.getD (0,0)=pair A B I' J') :
    Budget (CountLayers.cell A B binom k q w prev I J (I.sort (· ≤ ·)).head?)
      (· = pair A B I J) (cellCost m) := by
  by_cases hq : q=0
  · have hi : I=∅ := card_eq_zero.mp (hc.trans hq)
    have hj : J=∅ := card_eq_zero.mp (hd.trans hq)
    subst I; subst J
    rw [hq]
    haveI : IsEmpty (Fin ((∅ : Finset (Fin m)).card)) := inferInstanceAs (IsEmpty (Fin 0))
    apply bLe (bPure ?_) (Nat.zero_le _)
    simp [pair,permMinor]
    exact ⟨Matrix.permanent_isEmpty.symm,Matrix.permanent_isEmpty.symm⟩
  · obtain ⟨i,xs,he⟩ : ∃ i xs, I.sort (· ≤ ·) = i::xs := by
      cases he : I.sort (· ≤ ·) with
      | nil => have hl := congrArg List.length he; simp [hc,hq] at hl
      | cons i xs => exact ⟨i,xs,rfl⟩
    have hi : i∈I := by rw [←mem_sort (· ≤ ·)]; simp [he]
    have hlo : ∀ x∈I.erase i, k-(q-1) ≤ x.val := by
      intro x hx
      obtain ⟨hne,hx⟩ := mem_erase.mp hx
      have hx' : x∈xs := by have := (mem_sort (· ≤ ·)).mpr hx; simpa [he,hne] using this
      have hlt := I.sortedLT_sort.pairwise
      rw [he] at hlt
      have hix : i.val < x.val := List.pairwise_cons.mp hlt |>.1 x hx'
      have := hlow i hi
      omega
    have hf := colFoldBudget A B hA hB binom ht prev w (key (k-(q-1)) (I.erase i)) i I J hi
      (hd.trans hc.symm) (fun j hj => hold (by omega) _ _ (by rw [card_erase_of_mem hi,hc])
        (by rw [card_erase_of_mem hj,hd]) hlo)
    simp only [CountLayers.cell,if_neg hq,he,List.head?_cons]
    refine bLe (bTick (bBind (w := 8*(m+1)^3+m*colStepCost m) (rankBudget binom _ (I.erase i) ht) ?_)) (by dsimp [cellCost]; omega)
    intro r hr; subst r
    apply bTick
    exact hf
end LargeDP

end

section
open CapacitatedAssort.General BipHamCount.Deterministic Finset
namespace ColexBounds
def digits {m : ℕ} (lo : ℕ) (U : Finset (Fin m)) : List ℕ :=
  ((U.sort (· ≤ ·)).map (fun i => i.val-lo)).reverse

theorem digits_length {m : ℕ} (lo : ℕ) (U : Finset (Fin m)) : (digits lo U).length=U.card := by
  simp [digits]

private theorem digits_decrease {m : ℕ} (lo : ℕ) (U : Finset (Fin m)) (hu : ∀ i ∈ U, lo ≤ i.val) :
    (digits lo U).Pairwise (· > ·) := by
  rw [digits,List.pairwise_reverse,List.pairwise_map]
  apply U.sortedLT_sort.pairwise.imp_of_mem
  intro i j hi hj hij
  have hlow := hu i (by simpa using hi)
  change i.val < j.val at hij
  change i.val-lo < j.val-lo
  omega

theorem digits_inj {m : ℕ} {lo : ℕ} {U V : Finset (Fin m)} (hu : ∀ i ∈ U, lo ≤ i.val)
    (hv : ∀ i ∈ V, lo ≤ i.val) (he : digits lo U = digits lo V) : U=V := by
  ext i
  have hset (W : Finset (Fin m)) (hw : ∀ j ∈ W, lo ≤ j.val) (hi : lo ≤ i.val) :
      i ∈ W ↔ i.val-lo ∈ digits lo W := by
    simp only [digits,List.mem_reverse,List.mem_map,Finset.mem_sort]
    refine ⟨fun h => ⟨i,h,rfl⟩,?_⟩
    rintro ⟨j,hj,he⟩
    have h := hw j hj
    have eq : j=i := Fin.ext (by omega)
    simpa [eq] using hj
  by_cases hi : lo ≤ i.val
  · rw [hset U hu hi,hset V hv hi,he]
  · exact ⟨fun h => (hi (hu _ h)).elim,fun h => (hi (hv _ h)).elim⟩

theorem rank_in_range {m lo : ℕ} (U : Finset (Fin m)) (hu : ∀ i ∈ U, lo ≤ i.val) :
    rank (digits lo U) < (m-lo).choose U.card := by
  rw [←digits_length lo U]
  apply rank_lt _ (digits_decrease lo U hu)
  intro j hj
  obtain ⟨i,hi,rfl⟩ : ∃ i ∈ U, i.val-lo=j := by simpa [digits] using hj
  have hlow := hu i hi
  have h := i.isLt
  omega

theorem rank_layer_inj {m lo : ℕ} {U V : Finset (Fin m)}
    (hu : ∀ i ∈ U, lo ≤ i.val) (hv : ∀ i ∈ V, lo ≤ i.val) (hcard : U.card=V.card)
    (hr : rank (digits lo U)=rank (digits lo V)) : U=V :=
  digits_inj hu hv (rank_inj _ _ (digits_decrease lo U hu) (digits_decrease lo V hv)
    (by simpa only [digits_length] using hcard) hr)
end ColexBounds

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic ColexBounds
namespace CountLayers
def finishEntry {m} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k q ix : ℕ)
    (I J : Finset (Fin m)) (st : StepState) (p : Pair) : Work (ForInStep StepState) := do
  charge ((m+1)^2+8*(m+1)^3)
  let cur := st.2.set! ix p
  charge (2*(m+1))
  if k < q ∧ v ∉ I then
    let z ← largeSummand A B I J p.1 p.2
    let a ← zadd st.1 z
    return .yield (a,cur)
  else return .yield (st.1,cur)

theorem entry_eq {m} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (binom : Array (Array ℕ))
    (k q prevWidth nc ri : ℕ) (prev : Table) (I : Finset (Fin m)) (first : Option (Fin m))
    (J : Finset (Fin m)) (st : StepState) :
    entryStep A B v binom k q prevWidth nc ri prev I first J st = (do
      charge (4*(m+1))
      let rj ← colex binom 0 J
      let p ← cell A B binom k q prevWidth prev I J first
      finishEntry A B v k q (ri*nc+rj) I J st p) := by
  by_cases hq : q=0 <;> cases first <;> by_cases h : k < q ∧ v ∉ I <;>
    simp [entryStep,cell,finishEntry,hq,h,bind_assoc]
end CountLayers

end

section

namespace LargeDP
open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel Finset
open scoped BigOperators Matrix

noncomputable def gain {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k q : ℕ)
    (I J : Finset (Fin m)) : ℤ := if k < q ∧ v∉I then sigmaTerm A B I J else 0

def termWidth (m : ℕ) := LargeSumm.outSize m (m*m)
def accumCost (m u : ℕ) := (u+termWidth m+3)^2
def finishCost (m u : ℕ) :=
  ((m+1)^2+8*(m+1)^3) + 2*(m+1) + LargeSumm.cost m (m*m) + accumCost m u
def entryCost (m u : ℕ) := 4*(m+1)+addressCost m+cellCost m+finishCost m u

theorem gain_bound {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (k q : ℕ) (I J : Finset (Fin m)) (hc : J.card=I.card) :
    (gain A B v k q I J).natAbs ≤ 2^(termWidth m) := by
  unfold gain
  split
  · have hp := LargeSumm.large_summand_budget A B hA hB I J hc _ _ (m*m)
        (permMinor_power A hA I J) (permMinor_power B hB J I)
    obtain ⟨h,hb⟩ := (hp.run 0).1
    rw [h] at hb
    exact hb
  · simp

theorem finish_budget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (k q ix u : ℕ) (I J : Finset (Fin m)) (hc : J.card=I.card) (st : CountLayers.StepState)
    (hu : st.1.natAbs ≤ 2^u) :
    Budget (CountLayers.finishEntry A B v k q ix I J st (pair A B I J))
       (· = .yield (st.1+gain A B v k q I J,st.2.set! ix (pair A B I J))) (finishCost m u) := by
  have hsize (q b : ℕ) (h : q ≤ 2^b) : q.size ≤ b+1 :=
    Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos b; omega))
  by_cases h : k < q ∧ v∉I
  · simp only [CountLayers.finishEntry,if_pos h,gain]
    have hp := LargeSumm.large_summand_budget A B hA hB I J hc _ _ (m*m)
        (permMinor_power A hA I J) (permMinor_power B hB J I)
    refine bLe (bTick (bTick (bBind (w := accumCost m u) hp ?_))) (by unfold finishCost; omega)
    intro z hz
    have hzadd : Budget (zadd st.1 z) (·=st.1+z) (accumCost m u) := by
      constructor; intro s; refine ⟨rfl,?_⟩
      change s+(st.1.natAbs.size+z.natAbs.size+1)^2 ≤ _
      apply Nat.add_le_add_left
      apply Nat.pow_le_pow_left
      have hu' := hsize _ _ hu
      have hz' := hsize _ (termWidth m) hz.2
      omega
    refine bLe (bBind (w:=0) hzadd ?_) (by omega)
    intro x hx
    apply bPure
    rw [hx,hz.1]
    rfl
  · simp only [CountLayers.finishEntry,if_neg h,gain,add_zero]
    exact bLe (bTick (bTick (bPure rfl))) (by unfold finishCost; omega)

theorem entry_budget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (binom : Array (Array ℕ)) (ht : ∀ r j, r < m → j ≤ m → ((binom[r]?.getD #[])[j]?.getD 0)=r.choose j)
    (prev : Array (ℤ × ℤ)) (w k q nc ri u : ℕ) (I J : Finset (Fin m)) (hc : I.card=q) (hd : J.card=q)
    (hlow : ∀ x∈I, k-q ≤ x.val)
    (hold : 0 < q → ∀ I' J' : Finset (Fin m), I'.card=q-1 → J'.card=q-1 → (∀ x∈I', k-(q-1) ≤ x.val) →
      prev[key (k-(q-1)) I'*w+key 0 J']?.getD (0,0)=pair A B I' J')
    (st : CountLayers.StepState) (hu : st.1.natAbs ≤ 2^u) :
    Budget (CountLayers.entryStep A B v binom k q w nc ri prev I (I.sort (· ≤ ·)).head? J st)
      (· = .yield (st.1+gain A B v k q I J,st.2.set! (ri*nc+key 0 J) (pair A B I J))) (entryCost m u) := by
  rw [CountLayers.entry_eq]
  refine bLe (bTick (bBind (w := cellCost m+finishCost m u) (rankBudget binom 0 J ht) ?_)) (by unfold entryCost; omega)
  intro r hr; subst r
  apply bBind (cell_budget A B hA hB binom ht prev w k q I J hc hd hlow hold)
  intro p hp; subst p
  exact finish_budget A B hA hB v k q _ u I J (hd.trans hc.symm) st hu
end LargeDP

end

section
open BipHamCount.Deterministic BerkowitzModel
namespace LargeDP

def uniformWidth (m : ℕ) := termWidth m + 3*m+3

theorem uniform_bound (m : ℕ) : ((m+1)*4^m)*2^(termWidth m) ≤ 2^(uniformWidth m) := by
  have h : m+1 ≤ 2^(m+1) := Nat.lt_two_pow_self.le
  calc
    _ ≤ (2^(m+1)*4^m)*2^(termWidth m) := by gcongr
    _ = 2^(m+1+2*m+termWidth m) := by
      rw [show (4:ℕ)=2^2 by decide, ←pow_mul,←pow_add,←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold uniformWidth; omega)

private def UniformDP_PolyBound (f : ℕ → ℕ) := ∃ K d : ℕ, ∀ m, f m ≤ K*(m+1)^d
private theorem UniformDP_poly_id : UniformDP_PolyBound (fun m => m) := ⟨1,1,by intro m; simp⟩
private theorem UniformDP_poly_const (k : ℕ) : UniformDP_PolyBound (fun _ => k) := ⟨k,0,by simp⟩
private theorem UniformDP_poly_add {f g : ℕ → ℕ} (hf : UniformDP_PolyBound f) (hg : UniformDP_PolyBound g) :
    UniformDP_PolyBound (fun m => f m + g m) := by
  obtain ⟨K,a,hf⟩ := hf
  obtain ⟨L,b,hg⟩ := hg
  refine ⟨K+L,a+b,fun m => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hf m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
    ((hg m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
private theorem UniformDP_poly_mul {f g : ℕ → ℕ} (hf : UniformDP_PolyBound f) (hg : UniformDP_PolyBound g) :
    UniformDP_PolyBound (fun m => f m*g m) := by
  obtain ⟨K,a,hf⟩ := hf; obtain ⟨L,b,hg⟩ := hg
  refine ⟨K*L,a+b,fun m => ?_⟩
  exact (Nat.mul_le_mul (hf m) (hg m)).trans_eq (by rw [pow_add]; ring)
private theorem UniformDP_poly_pow {f : ℕ → ℕ} (p : ℕ) (hf : UniformDP_PolyBound f) :
    UniformDP_PolyBound (fun m => (f m)^p) := by
  obtain ⟨K,a,hf⟩ := hf
  refine ⟨K^p,a*p,fun m => ?_⟩
  exact (Nat.pow_le_pow_left (hf m) _).trans_eq (by rw [mul_pow,pow_mul])

set_option maxHeartbeats 2000000 in
theorem uniform_cost_polynomial : ∃ K d : ℕ, ∀ m, entryCost m (uniformWidth m) ≤ K*(m+1)^d := by
  change UniformDP_PolyBound (fun m => entryCost m (uniformWidth m))
  dsimp only [entryCost,uniformWidth,termWidth,finishCost,accumCost,cellCost,colStepCost,
    addressCost,readCost,arithmeticCost,widthLimit,LargeSumm.cost,LargeSumm.outSize,
    LargeSumm.minorTime,determinantTime,coefficientTime,layerTime3,layerTime2,layerTime1,
    basicTime,opCost,cap,cBound,tBound,vBound]
  repeat' first
  | with_reducible exact UniformDP_poly_id
  | with_reducible exact UniformDP_poly_const _
  | with_reducible refine UniformDP_poly_pow _ ?_
  | with_reducible refine UniformDP_poly_mul ?_ ?_
  | with_reducible refine UniformDP_poly_add ?_ ?_
end LargeDP

end

section
open CapacitatedAssort.General
namespace BipHamCount.Deterministic
private def insertLoop {m : ℕ} (i : Fin m) (xs acc : List (Finset (Fin m))) : Work (List (Finset (Fin m))) := do
  let mut out := acc
  for x in xs do
    charge (m+3)
    out := insert i x :: out
  return out

private theorem insertLoop_run {m : ℕ} (i : Fin m) (xs acc : List (Finset (Fin m))) (s : ℕ) :
    (insertLoop i xs acc).run s = ((xs.map (insert i)).reverse ++ acc, s + (m+3)*xs.length) := by
  induction xs generalizing acc s with
  | nil => change (acc,s) = _; simp
  | cons x xs ih =>
    have eqn : (insertLoop i (x::xs) acc).run s =
        (insertLoop i xs (insert i x :: acc)).run (s+(m+3)) := by
      simp [insertLoop, charge, StateT.run_bind]
    rw [eqn,ih]
    simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem chooseSets_spec {m : ℕ} (xs : List (Fin m)) (q s : ℕ) :
    ((chooseSets xs q).run s).1.Perm ((xs.sublistsLen q).map List.toFinset) ∧
    ((chooseSets xs q).run s).2 ≤ s + (m+4)*(3*(xs.length+1)*(xs.length.choose q)+1) := by
  induction xs generalizing s q with
  | nil =>
    cases q with
    | zero => change [∅].Perm _ ∧ s+2 ≤ _; simp; omega
    | succ q => change [].Perm _ ∧ s+1 ≤ _; simp
  | cons i xs ih =>
    cases q with
    | zero => change [∅].Perm _ ∧ s+2 ≤ _; simp; nlinarith
    | succ q =>
      by_cases h : xs.length < q
      · have e : (chooseSets (i::xs) (q+1)).run s = ([],s+(m+4)) := by
          simp [chooseSets, h, charge, StateT.run_bind]; rfl
        have hn : (i::xs).length < q+1 := by simpa
        rw [e, List.sublistsLen_of_length_lt hn, Nat.choose_eq_zero_of_lt hn]; simp
      · let a := (chooseSets xs q).run (s+(m+4))
        let b := (chooseSets xs (q+1)).run a.2
        have e : (chooseSets (i::xs) (q+1)).run s =
            (insertLoop i a.1 b.1).run b.2 := by
          simp [chooseSets, h, insertLoop, a, b, charge, StateT.run_bind]; rfl
        obtain ⟨ha,hat⟩ := ih q (s+(m+4))
        change a.1.Perm _ at ha
        change a.2 ≤ _ at hat
        obtain ⟨hb,hbt⟩ := ih (q+1) a.2
        change b.1.Perm _ at hb
        change b.2 ≤ _ at hbt
        rw [e,insertLoop_run]
        simp only [List.length_cons, Nat.choose_succ_succ, List.sublistsLen_succ_cons,
          List.map_append, List.map_map, Prod.fst, Prod.snd]
        constructor
        · apply List.perm_append_comm.trans
          apply hb.append
          have hh := ((List.reverse_perm _).trans (ha.map (insert i)))
          simpa [List.map_map,Function.comp_def] using hh
        · have hlen : a.1.length = xs.length.choose q := by simpa using ha.length_eq
          rw [hlen]
          have hpos := Nat.choose_pos (Nat.le_of_not_gt h)
          nlinarith [Nat.mul_le_mul_left (m+4) (show 1 ≤ xs.length.choose q from hpos)]
end BipHamCount.Deterministic

end

section
open CapacitatedAssort.General
namespace BipHamCount.Deterministic
private abbrev Pair (m : ℕ) := Finset (Fin m) × Finset (Fin m)
private def three {m : ℕ} (i : Fin m) (p : Pair m) : List (Pair m) :=
  [(insert i p.1,p.2),(p.1,insert i p.2),(insert i p.1,insert i p.2)]

private def strip {m : ℕ} (i : Fin m) (p : Pair m) : Pair m := (p.1.erase i,p.2.erase i)

private def labelLoop {m : ℕ} (i : Fin m) (pairs acc : List (Pair m)) : Work (List (Pair m)) := do
  let mut out := acc
  for p in pairs do
    charge (4*(m+1)+4)
    let x := insert i p.1
    let y := insert i p.2
    out := (x,p.2) :: (p.1,y) :: (x,y) :: out
  return out

private lemma labelLoop_val {m : ℕ} (i : Fin m) (pairs acc : List (Pair m)) (s : ℕ) :
    ((labelLoop i pairs acc).run s).1 = pairs.reverse.flatMap (three i) ++ acc := by
  induction pairs generalizing acc s with
  | nil => rfl
  | cons p ps ih =>
    let next := three i p ++ acc
    have hstep : (labelLoop i (p::ps) acc).run s =
        (labelLoop i ps next).run (s + (4*(m+1)+4)) := by
      simp [labelLoop, charge, next, three, StateT.run_bind]
    rw [hstep,ih]
    simp [next, List.flatMap_append, List.append_assoc]

private theorem strip_of_mem {m : ℕ} {i : Fin m} {p t : Pair m}
    (hp : i ∉ p.1 ∪ p.2) (ht : t ∈ three i p) : strip i t = p := by
  obtain ⟨ha,hb⟩ : i ∉ p.1 ∧ i ∉ p.2 := by simpa using hp
  simp only [three, List.mem_cons,List.not_mem_nil, or_false] at ht
  rcases ht with rfl|rfl|rfl <;> simp [strip, ha,hb]

private theorem three_nodup {m : ℕ} {i : Fin m} {p : Pair m} (hp : i ∉ p.1 ∪ p.2) :
    (three i p).Nodup := by
  obtain ⟨ha,hb⟩ : i ∉ p.1 ∧ i ∉ p.2 := by simpa using hp
  have ha' : insert i p.1 ≠ p.1 := fun h => ha (h ▸ Finset.mem_insert_self i p.1)
  have hb' : insert i p.2 ≠ p.2 := fun h => hb (h ▸ Finset.mem_insert_self i p.2)
  simp [three,Prod.ext_iff,ha',hb',Ne.symm ha',Ne.symm hb']

private lemma mem_from_strip {m : ℕ} (i : Fin m) (t : Pair m) (h : i ∈ t.1 ∪ t.2) :
    t ∈ three i (strip i t) := by
  rcases t with ⟨a,b⟩
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;>
    simp_all [three,strip,Finset.erase_eq_of_notMem,Finset.insert_erase]

/-- Three-way labelling enumerates each ordered pair with the prescribed union once. -/
theorem labelPairs_spec {m : ℕ} (xs : List (Fin m)) (hn : xs.Nodup) (s : ℕ) :
    ((labelPairs xs).run s).1.Nodup ∧
    ∀ t : Finset (Fin m) × Finset (Fin m), t ∈ ((labelPairs xs).run s).1 ↔ t.1 ∪ t.2 = xs.toFinset := by
  induction xs generalizing s with
  | nil =>
    change [(∅,∅)].Nodup ∧ ∀ t : Pair m, t ∈ [(∅,∅)] ↔ t.1 ∪ t.2 = ∅
    simp [Prod.ext_iff]
  | cons i xs ih =>
    let sub := (labelPairs xs).run (s+1)
    have ⟨hi,hn'⟩ := List.nodup_cons.mp hn
    have hnot : i ∉ xs.toFinset := by simpa using hi
    obtain ⟨hd,hm⟩ := ih hn' (s+1)
    change sub.1.Nodup at hd
    change ∀ t : Pair m, t ∈ sub.1 ↔ t.1 ∪ t.2 = xs.toFinset at hm
    have hp {p : Pair m} (h : p ∈ sub.1.reverse) : i ∉ p.1 ∪ p.2 := by
      rw [(hm p).mp (List.mem_reverse.mp h)]
      exact hnot
    have hb : (labelPairs (i::xs)).run s = (labelLoop i sub.1 []).run sub.2 := rfl
    rw [hb,labelLoop_val,List.append_nil]
    constructor
    · apply List.nodup_flatMap.mpr
      refine ⟨fun p h => three_nodup (hp h), ?_⟩
      apply List.Pairwise.imp_of_mem (l := sub.1.reverse) (R := (· ≠ ·)) _ (List.nodup_reverse.mpr hd)
      intro p q h₁ h₂ hpq
      apply List.disjoint_left.mpr
      intro t htp htq
      exact hpq ((strip_of_mem (hp h₁) htp).symm.trans (strip_of_mem (hp h₂) htq))
    · intro t
      rw [List.mem_flatMap, List.toFinset_cons]
      constructor
      · rintro ⟨p,hp',ht⟩
        have he := (hm p).mp (List.mem_reverse.mp hp')
        simp only [three,List.mem_cons,List.not_mem_nil, or_false] at ht
        rcases ht with rfl|rfl|rfl <;> simp [←he,Finset.insert_union,Finset.union_insert]
      · intro ht
        have hi' : i ∈ t.1 ∪ t.2 := ht ▸ Finset.mem_insert_self _ _
        refine ⟨strip i t, List.mem_reverse.mpr ((hm _).mpr ?_), mem_from_strip i t hi'⟩
        change t.1.erase i ∪ t.2.erase i = xs.toFinset
        have hu : t.1.erase i ∪ t.2.erase i = (t.1 ∪ t.2).erase i := by
          ext v; simp only [Finset.mem_union,Finset.mem_erase]; tauto
        rw [hu,ht,Finset.erase_insert hnot]
end BipHamCount.Deterministic

end

section
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

end

section
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

end

section
open CapacitatedAssort.General Finset
namespace BipHamCount.Deterministic

private theorem filtered_suffix_length (m lo : ℕ) :
    ((List.finRange m).filter (fun i => decide (lo ≤ i.val))).length=m-lo := by
  classical
  let xs := (List.finRange m).filter (fun i => decide (lo ≤ i.val))
  have hn : xs.Nodup := (List.nodup_finRange m).filter _
  change xs.length=_
  rw [←List.toFinset_card_of_nodup hn]
  by_cases hlo : lo < m
  · let v : Fin m := ⟨lo,hlo⟩
    have he : xs.toFinset=Finset.Ici v := by ext i; simp [xs,v,Fin.le_def]
    rw [he,Fin.card_Ici]
  · have he : xs.toFinset=∅ := by
      ext i
      have hi : ¬ (lo ≤ i.val) := by have := i.isLt; omega
      simp [xs,hi]
    rw [he]; simp; omega

theorem large_layer_count (m k q s₁ s₂ s₃ s₄ : ℕ) :
    ((chooseSets ((suffix (m:=m) (k-q)).run s₁).1 q).run s₂).1.length *
    ((chooseSets ((suffix (m:=m) 0).run s₃).1 q).run s₄).1.length =
      (m-(k-q)).choose q * m.choose q := by
  rw [suffix_run,suffix_run]
  simp only
  rw [(chooseSets_spec _ _ _).1.length_eq,(chooseSets_spec _ _ _).1.length_eq]
  simp only [List.length_map,List.length_sublistsLen,filtered_suffix_length,Nat.sub_zero]
end BipHamCount.Deterministic

end

section
open CapacitatedAssort.General BerkowitzModel

namespace TableGrid
abbrev State (V : Type) := Array V × ℤ

def writeAt {K V : Type} (ix : K → ℕ) (val : K → V) (gain : K → ℤ) (a : State V) (k : K) :
    State V := (a.1.set! (ix k) (val k),a.2+gain k)

theorem fold_resume {K S : Type} (xs : List K) (step : K → S → Work (ForInStep S))
    (f : S → K → S) (s : S) (h : ∀ k ∈ xs, ∀ a, Post (step k a) (· = .yield (f a k))) :
    Post (forIn xs s step) (· = xs.foldl f s) := by
  induction xs generalizing s with
  | nil => simpa using purePost (x:=s) (Q:=fun a => a=s) rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (h x (by simp) s)
    intro y hy
    subst y
    exact ih _ (fun k hk => h k (by simp [hk]))

theorem writes_spec {K V : Type} (xs : List K) (ix : K → ℕ) (val : K → V) (gain : K → ℤ)
    (a : State V) (hbound : ∀ x ∈ xs, ix x < a.1.size)
    (compat : ∀ x ∈ xs, ∀ y ∈ xs, ix x=ix y → val x=val y) :
    let out := xs.foldl (writeAt ix val gain) a
    out.1.size=a.1.size ∧ out.2=a.2+(xs.map gain).sum ∧
    (∀ x ∈ xs, out.1[ix x]? = some (val x)) ∧
    (∀ j, (∀ x ∈ xs, ix x ≠ j) → out.1[j]?=a.1[j]?) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    let b := writeAt ix val gain a x
    have hbs : b.1.size=a.1.size := by simp [b,writeAt,Array.set!_eq_setIfInBounds]
    have hxt : ∀ y ∈ xs, ix y < b.1.size := fun y hy => (hbound y (by simp [hy])).trans_eq hbs.symm
    obtain ⟨hs,ht,hd,ho⟩ := ih b hxt (fun z hz y hy => compat z (by simp [hz]) y (by simp [hy]))
    change _ ∧ _ ∧ _ ∧ _
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,List.mem_cons]
    refine ⟨hs.trans hbs,by simpa [b,writeAt,add_assoc] using ht,?_,?_⟩
    · intro z hz
      rcases hz with rfl|hz
      · by_cases hex : ∃ y ∈ xs, ix y=ix z
        · obtain ⟨y,hy,he⟩ := hex
          rw [←he,hd y hy,compat y (by simp [hy]) z (by simp) he]
        · have hx := ho (ix z) (fun y hy h => hex ⟨y,hy,h⟩)
          rw [hx]
          exact Array.getElem?_setIfInBounds_self_of_lt (hbound z (by simp))
      · exact hd z hz
    · intro j hj
      rw [ho j (fun y hy => hj y (Or.inr hy))]
      exact Array.getElem?_setIfInBounds_ne (hj x (Or.inl rfl))

theorem grid_eval {R C V : Type} (rows : List R) (cols : List C) (a : State V)
    (ix : R × C → ℕ) (val : R × C → V) (gain : R × C → ℤ)
    (outer : R → State V → Work (ForInStep (State V)))
    (hrow : ∀ r ∈ rows, ∀ a,
      Post (outer r a) (· = .yield (cols.foldl (fun acc c => writeAt ix val gain acc (r,c)) a))) :
    Post (forIn rows a outer)
      (· = (rows.flatMap (fun r => cols.map (fun c => (r,c)))).foldl (writeAt ix val gain) a) := by
  apply postMono (fold_resume rows outer _ a hrow)
  intro out hout
  rw [hout]
  clear hrow hout
  induction rows generalizing a with
  | nil => rfl
  | cons r rs ih => simp [List.foldl_append,List.foldl_map,ih]
end TableGrid

end

section
open BipHamCount.Deterministic Finset
namespace ColexBounds
def pairAddress {m : ℕ} (lo width : ℕ) (p : Finset (Fin m) × Finset (Fin m)) : ℕ :=
  rank (digits lo p.1)*width + rank (digits 0 p.2)

theorem pairAddress_lt {m lo q : ℕ} (p : Finset (Fin m) × Finset (Fin m))
    (hR : ∀ i ∈ p.1, lo ≤ i.val) (hI : p.1.card=q) (hJ : p.2.card=q) :
    pairAddress lo (m.choose q) p < (m-lo).choose q * m.choose q := by
  have hr := rank_in_range p.1 hR
  have hc := rank_in_range p.2 (lo:=0) (fun _ _ => Nat.zero_le _)
  simp only [hI,hJ,Nat.sub_zero] at hr hc
  unfold pairAddress
  have h := Nat.mul_le_mul_right (m.choose q) (Nat.succ_le_of_lt hr)
  rw [Nat.succ_mul] at h; omega

theorem pairAddress_inj {m lo q : ℕ} {p p' : Finset (Fin m) × Finset (Fin m)}
    (hu : ∀ i ∈ p.1, lo ≤ i.val) (hv : ∀ i ∈ p'.1, lo ≤ i.val)
    (hi : p.1.card=q) (hi' : p'.1.card=q) (hj : p.2.card=q) (hj' : p'.2.card=q)
    (he : pairAddress lo (m.choose q) p=pairAddress lo (m.choose q) p') : p=p' := by
  have a := rank_in_range p.2 (lo:=0) (fun _ _ => Nat.zero_le _)
  have b := rank_in_range p'.2 (lo:=0) (fun _ _ => Nat.zero_le _)
  simp only [Nat.sub_zero,hj,hj'] at a b
  have hc := congrArg (· % m.choose q) he
  simp only [pairAddress,Nat.mul_add_mod_of_lt a,Nat.mul_add_mod_of_lt b] at hc
  have hr := congrArg (· / m.choose q) he
  have hpos : 0 < m.choose q := by omega
  simp only [pairAddress, Nat.mul_comm _ (m.choose q), Nat.mul_add_div hpos,
    Nat.div_eq_of_lt a,Nat.div_eq_of_lt b,Nat.add_zero] at hr
  exact Prod.ext (rank_layer_inj hu hv (hi.trans hi'.symm) hr)
    (rank_layer_inj (lo:=0) (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) (hj.trans hj'.symm) hc)
end ColexBounds

end

section
open CapacitatedAssort.General Finset BipHamCount.Deterministic ColexBounds
open scoped BigOperators
namespace CountLayers

def allowed {m : ℕ} (lo : ℕ) := (univ : Finset (Fin m)).filter (fun i => lo ≤ i.val)
theorem sets_by_layer {m : ℕ} (xs : List (Fin m)) (hn : xs.Nodup) (q s : ℕ) :
    ((chooseSets xs q).run s).1.Perm (xs.toFinset.powersetCard q).toList := by
  classical
  let sets := xs.toFinset.powersetCard q
  let gen := (xs.sublistsLen q).map List.toFinset
  apply (chooseSets_spec xs q s).1.trans
  have sub : sets.toList ⊆ gen := by
    intro U hU
    obtain ⟨hin,hcard⟩ := Finset.mem_powersetCard.mp (Finset.mem_toList.mp hU)
    let vs := xs.filter fun v => decide (v ∈ U)
    have he : vs.toFinset=U := by
      ext v; simp only [vs,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      exact ⟨And.right,fun h => ⟨List.mem_toFinset.mp (hin h),h⟩⟩
    have hl : vs.length=q := by rw [←List.toFinset_card_of_nodup (hn.filter _),he,hcard]
    exact List.mem_map.mpr ⟨vs,List.mem_sublistsLen.mpr ⟨List.filter_sublist,hl⟩,he⟩
  obtain ⟨z,hz,ht⟩ := List.subperm_iff.mp (sets.nodup_toList.subperm sub)
  have hl : gen.length = sets.toList.length := by simp [gen,sets,Finset.card_powersetCard,List.toFinset_card_of_nodup hn]
  have he := ht.eq_of_length (hz.length_eq.trans hl).symm
  exact (he ▸ hz).symm

theorem row_set_perm {m : ℕ} (lo q s t : ℕ) :
    ((chooseSets ((suffix (m:=m) lo).run s).1 q).run t).1.Perm
      (((allowed (m:=m) lo).powersetCard q).toList) := by
  rw [suffix_run]
  let xs := (List.finRange m).filter (fun i => decide (lo ≤ i.val))
  have he : xs.toFinset=allowed lo := by ext i; simp [xs,allowed]
  rw [←he]; apply sets_by_layer; exact (List.nodup_finRange m).filter _

private def isTerm {m : ℕ} (v : Fin m) (k q : ℕ) (I : Finset (Fin m)) := k < q ∧ v ∉ I
open Classical in
noncomputable def layerSum {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k q : ℕ) :=
  ∑ I ∈ (allowed (m:=m) (k-q)).powersetCard q, ∑ J ∈ (univ : Finset (Fin m)).powersetCard q,
    if k < q ∧ v ∉ I then sigmaTerm A B I J else 0

theorem layerSum_sigma {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    (∑ q ∈ range (m+1), layerSum A B v k q) = sigmaLarge A B v k := by
  classical
  have hl (q : ℕ) :
      layerSum A B v k q =
      ∑ I : Finset (Fin m), ∑ J : Finset (Fin m),
      if I.card=q ∧ J.card=q ∧ k < q ∧ v ∉ I then sigmaTerm A B I J else 0 := by
    by_cases h : k < q
    · have hg : allowed (m:=m) (k-q)=univ := by ext; simp [allowed,show k-q=0 by omega]
      have ht : (univ : Finset (Fin m)).powersetCard q = univ.filter (fun x => x.card=q) := by ext; simp
      simp only [layerSum,hg,ht,Finset.sum_filter]
      apply Finset.sum_congr rfl; intro I _
      by_cases hi : I.card=q <;> by_cases hv : v ∈ I <;> simp [hi,hv,h]
    · simp [layerSum,h]
  simp_rw [hl]
  rw [Finset.sum_comm]
  unfold sigmaLarge
  have hu : (univ.erase v).powerset = univ.filter (fun I : Finset (Fin m) => v ∉ I) := by
    ext I
    simp only [mem_powerset,mem_filter,mem_univ,true_and,Finset.subset_erase]
    simp
  rw [hu]
  have hall : (univ : Finset (Fin m)).powerset=univ := by ext; simp
  simp only [hall,Finset.sum_filter]
  apply Finset.sum_congr rfl; intro I _
  rw [Finset.sum_comm]
  have hh : I.card < m+1 := by simpa using Nat.lt_succ_of_le (Finset.card_le_univ I)
  have inner (J : Finset (Fin m)) :
      (∑ q ∈ range (m+1), if I.card=q ∧ J.card=q ∧ k < q ∧ v ∉ I then sigmaTerm A B I J else 0) =
      if J.card=I.card ∧ k < I.card ∧ v ∉ I then sigmaTerm A B I J else 0 := by
    calc
      _ = ∑ q ∈ range (m+1), if I.card=q then
        (if J.card=I.card ∧ k < I.card ∧ v ∉ I then sigmaTerm A B I J else 0) else 0 := by
          apply Finset.sum_congr rfl; intro q _
          by_cases hq : I.card=q
          · subst q; simp
          · simp [hq]
      _ = _ := by simp [hh]
  simp_rw [inner]
  by_cases hi : v ∈ I <;> by_cases hk : k < I.card <;> simp [hi,hk]
end CountLayers

end

section
open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel

namespace LargeDP
structure NatPrefix {α : Type} (a : Array α) (d : α) (n : ℕ) (P : ℕ → α → Prop) : Prop where
  size : a.size=n
  read : ∀ i < n, P i (a[i]?.getD d)

private theorem start {α : Type} {d : α} {P : ℕ → α → Prop} : NatPrefix #[] d 0 P :=
  ⟨rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩
private theorem push {α : Type} {d x : α} {a : Array α} {P : ℕ → α → Prop} {n : ℕ}
    (ha : NatPrefix a d n P) (hx : P n x) : NatPrefix (a.push x) d (n+1) P := by
  refine ⟨by simp [ha.size],?_⟩
  intro i hi; rw [Array.getElem?_push,ha.size]
  by_cases h : i=n
  · subst i; simpa using hx
  · rw [if_neg h]; exact ha.read i (by omega)

def pascalTime (m : ℕ) := 4*(m+1)+1+(m+1)*(4*(m+1)+1+(m+1)*(8*(m+1)^2)+1)

theorem pascal (m : ℕ) : Budget (binomTable m) (fun t => ∀ i ≤ m, ∀ j ≤ m,
    ((t[i]?.getD #[])[j]?.getD 0)=i.choose j) (pascalTime m) := by
  let rowOK := fun (r : ℕ) (a : Array ℕ) => ∀ j ≤ m, a[j]?.getD 0 = r.choose j
  let I := fun r (state : Array (Array ℕ) × Array ℕ) =>
    NatPrefix state.1 #[] r rowOK ∧ (0 < r → rowOK (r-1) state.2)
  rw [binomTable]
  refine bLe (bTick (bBind (w := 0) (u := (m+1)*(4*(m+1)+1+(m+1)*(8*(m+1)^2)+1)) (Q := I (m+1)) ?_ ?_)) ?_
  · apply bRange I
    · exact ⟨start,fun h => (Nat.not_lt_zero _ h).elim⟩
    · intro r hr st hst
      refine bLe (bTick (bBind (w := 1+0) (u := (m+1)*(8*(m+1)^2)) (Q := fun row =>
        NatPrefix row 0 (m+1) (fun j x => x = r.choose j)) ?_ ?_)) (by omega)
      · apply bRange (fun k row => NatPrefix row 0 k (fun j x => x = r.choose j)) start
        intro j hj row hrow
        refine bLe (bTick (bPure ?_)) (by omega)
        apply push hrow
        change (if j=0 then 1 else if r=0 then 0 else _)=r.choose j
        cases j with
        | zero => simp
        | succ j =>
          cases r with
          | zero => simp
          | succ r =>
            simp only [Nat.succ_ne_zero,if_false,Nat.add_sub_cancel,Nat.succ_sub_succ_eq_sub,Nat.sub_zero]
            have hp := hst.2 (by omega)
            change (st.2[j]?.getD 0) + (st.2[j+1]?.getD 0) = _
            rw [hp j (by omega), hp (j+1) (by omega)]
            simp [Nat.choose_succ_succ]
      · intro row hrow
        apply bTick
        apply bPure
        have rr : rowOK r row := fun j hj => hrow.read j (by omega)
        exact ⟨push hst.1 rr,fun _ => by simpa using rr⟩
  · intro z hz; apply bPure
    exact fun i hi j hj => hz.1.read i (by omega) j hj
  · unfold pascalTime; omega

end LargeDP

end

section
open BipHamCount.Deterministic BerkowitzModel CapacitatedAssort.General
open scoped BigOperators
namespace LargeDP
abbrev Tensor (m : ℕ) := Matrix (Fin m) (Fin m) ℤ
def nEntries (m k q : ℕ) := (m-(k-q)).choose q*m.choose q
def layerRate (m : ℕ) := entryCost m (uniformWidth m) + 1000*(m+1)^5
def ready {m : ℕ} (A B : Tensor m) (k q : ℕ) (st : CountLayers.LayerState) : Prop :=
  (0 < q → ∀ I J : Finset (Fin m), I.card=q-1 → J.card=q-1 → (∀ i ∈ I, k-(q-1) ≤ i.val) →
    st.1[key (k-(q-1)) I*st.2.1 + key 0 J]?.getD (0,0)=pair A B I J) ∧
    st.2.2.natAbs ≤ q*4^m*2^(termWidth m)
def LayerContract {m : ℕ} (A B : Tensor m) (v : Fin m) (k : ℕ) : Prop :=
  ∀ (t : Array (Array ℕ)), (∀ i ≤ m, ∀ j ≤ m, ((t[i]?.getD #[])[j]?.getD 0)=i.choose j) →
  ∀ q ≤ m, ∀ st : CountLayers.LayerState, ready A B k q st →
    Budget (CountLayers.layerStep A B v t (List.finRange m) k q st)
      (Yield (fun o => ready A B k (q+1) o ∧ o.2.2=st.2.2+CountLayers.layerSum A B v k q))
      (nEntries m k q*layerRate m)
end LargeDP

end

section
open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel
open scoped BigOperators
namespace LargeDP

def totalEntries (m k : ℕ) := ∑ q ∈ Finset.range (m+1), nEntries m k q
def setup (m : ℕ) := pascalTime m+(4*m+1)+(m+3)*m+(4*(m+1)+1)

theorem program_budget {m : ℕ} (A B : Tensor m) (v : Fin m) (k : ℕ) (H : LayerContract A B v k) :
  Budget (largeTerms m A B v k) (·=sigmaLarge A B v k)
    (setup m + (m+1)*(totalEntries m k*layerRate m)) := by
  let I := fun q (st : CountLayers.LayerState) => ready A B k q st ∧
    st.2.2=∑ i ∈ Finset.range q, CountLayers.layerSum A B v k i
  have hi : I 0 (#[],0,0) := by simp [I,ready]
  let sCost := (4*m+1)+(m+3)*m
  let cCost := 4*(m+1)+1
  let w := (m+1)*(totalEntries m k*layerRate m)
  have hs : Budget (suffix (m:=m) 0) (· = List.finRange m) sCost := by
    constructor; intro s; rw [suffix_run]; simp [sCost,Nat.add_assoc]
  rw [CountLayers.factor,CountLayers.work]
  refine bLe (bBind (w:=sCost+cCost+w) (pascal m) ?_) (by dsimp [setup,sCost,cCost,w]; omega)
  intro t ht
  refine bLe (bBind (w:=cCost+w) hs ?_) (by omega)
  intro all hall; subst all
  apply bTick
  refine bLe (bBind (w:=0) (bRange (n:=m+1) (c:=totalEntries m k*layerRate m) I hi ?_) ?_) (by dsimp [w]; omega)
  · intro q hq st hst
    have h := H t ht q (by omega) st hst.1
    refine bWeaken h ?_ (Nat.mul_le_mul_right _ ?_)
    · intro o ho
      cases o with
      | done _ => exact False.elim ho
      | yield a =>
        refine ⟨ho.1,?_⟩
        change a.2.2=_
        rw [ho.2,hst.2,Finset.sum_range_succ]
    · exact Finset.single_le_sum (f:=fun i => nEntries m k i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_range.mpr hq)
  · intro st hst
    apply bPure
    exact hst.2.trans (CountLayers.layerSum_sigma A B v k)

end LargeDP

end

section
open BipHamCount.Deterministic BerkowitzModel
open scoped BigOperators
namespace LargeDP
private def PropTop_PolyBound (f : ℕ → ℕ) := ∃ K d : ℕ, ∀ m, f m ≤ K*(m+1)^d
private theorem PropTop_poly_id : PropTop_PolyBound (fun m => m) := ⟨1,1,by intro m; simp⟩
private theorem PropTop_poly_const (k : ℕ) : PropTop_PolyBound (fun _ => k) := ⟨k,0,by simp⟩
private theorem PropTop_poly_add {f g : ℕ → ℕ} (hf : PropTop_PolyBound f) (hg : PropTop_PolyBound g) :
    PropTop_PolyBound (fun m => f m + g m) := by
  obtain ⟨K,a,hf⟩ := hf
  obtain ⟨L,b,hg⟩ := hg
  refine ⟨K+L,a+b,fun m => ?_⟩
  rw [Nat.add_mul]
  exact Nat.add_le_add ((hf m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
    ((hg m).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
private theorem PropTop_poly_mul {f g : ℕ → ℕ} (hf : PropTop_PolyBound f) (hg : PropTop_PolyBound g) :
    PropTop_PolyBound (fun m => f m*g m) := by
  obtain ⟨K,a,hf⟩ := hf; obtain ⟨L,b,hg⟩ := hg
  refine ⟨K*L,a+b,fun m => ?_⟩
  exact (Nat.mul_le_mul (hf m) (hg m)).trans_eq (by rw [pow_add]; ring)
private theorem PropTop_poly_pow {f : ℕ → ℕ} (p : ℕ) (hf : PropTop_PolyBound f) :
    PropTop_PolyBound (fun m => (f m)^p) := by
  obtain ⟨K,a,hf⟩ := hf
  refine ⟨K^p,a*p,fun m => ?_⟩
  exact (Nat.pow_le_pow_left (hf m) _).trans_eq (by rw [mul_pow,pow_mul])

private theorem global_polynomial :
    ∃ K d : ℕ, ∀ m, setup m+(m+1)*layerRate m ≤ K*(m+1)^d := by
  have he : PropTop_PolyBound (fun m => entryCost m (uniformWidth m)) := uniform_cost_polynomial
  change PropTop_PolyBound _
  dsimp only [setup,pascalTime,layerRate]
  repeat' first
  | with_reducible exact he
  | with_reducible exact PropTop_poly_id
  | with_reducible exact PropTop_poly_const _
  | with_reducible refine PropTop_poly_pow _ ?_
  | with_reducible refine PropTop_poly_mul ?_ ?_
  | with_reducible refine PropTop_poly_add ?_ ?_

theorem from_layer_contract
    (layer : ∀ (m : ℕ) (A B : Tensor m), ZeroOne A → ZeroOne B → ∀ v : Fin m, LayerContract A B v (kOf m)) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B → ∀ v : Fin m,
        ((largeTerms m A B v (kOf m)).run 0).1 = sigmaLarge A B v (kOf m) ∧
        (((largeTerms m A B v (kOf m)).run 0).2 : ℝ) ≤ 
            C * ((m : ℝ)+1)^c * Real.exp (2*m*Real.binEntropy alpha) := by
  obtain ⟨K,d,hK⟩ := global_polynomial
  let R := (alpha/(1-alpha))^2
  have hR : 0 < R := by norm_num [R,alpha]
  refine ⟨(K+1)*R,by positivity,d+1,?_⟩
  intro m A B hA hB v
  obtain ⟨hv,hw⟩ := (program_budget A B v _ (layer m A B hA hB v)).run 0
  refine ⟨hv,?_⟩
  let N := totalEntries m (kOf m)
  have hN : 1 ≤ N := by
    have h := Finset.single_le_sum (f:=nEntries m (kOf m)) (fun _ _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (m+1) by simp)
    simpa [N,totalEntries,nEntries] using h
  have hc : ((largeTerms m A B v (kOf m)).run 0).2 ≤ N*((K+1)*(m+1)^d) := by
    have b : setup m ≤ N*setup m := by simpa using (Nat.mul_le_mul_right (setup m) hN)
    have x := (hK m).trans (Nat.mul_le_mul_right ((m+1)^d) (Nat.le_succ K))
    calc
      _ ≤ setup m + (m+1)*(N*layerRate m) := by simpa using hw
      _ ≤ N*(setup m+(m+1)*layerRate m) := by nlinarith only [b]
      _ ≤ _ := Nat.mul_le_mul_left N x
  have hr : (N:ℝ) ≤ ((m:ℝ)+1)*R*Real.exp (2*m*Real.binEntropy alpha) := by
    have h := largeTerms_layer_enumeration.2 m
    simpa [N,totalEntries,nEntries,Nat.cast_sum,Nat.cast_mul,mul_comm (m.choose _ : ℝ)] using h
  calc
    _ ≤ (N:ℝ)*(((K:ℝ)+1)*((m:ℝ)+1)^d) := by exact_mod_cast hc
    _ ≤ (((m:ℝ)+1)*R*Real.exp (2*m*Real.binEntropy alpha))*(((K:ℝ)+1)*((m:ℝ)+1)^d) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := by rw [pow_succ]; ring
end LargeDP

end

section
open CapacitatedAssort.General BerkowitzModel
namespace TableGrid

theorem countedFold {K S : Type} (xs : List K) (step : K → S → Work (ForInStep S))
    (f : S → K → S) (I : ℕ → S → Prop) (a : S) (c : ℕ) (h0 : I 0 a)
    (hstep : ∀ k ∈ xs, ∀ i < xs.length, ∀ a, I i a →
      Budget (step k a) (fun r => r = .yield (f a k) ∧ I (i+1) (f a k)) c) :
    Budget (forIn xs a step) (fun r => r=xs.foldl f a ∧ I xs.length r) (xs.length*c) := by
  have aux (ys : List K) (hy : ys ⊆ xs) (t : ℕ) (hl : t+ys.length=xs.length) (s : S) (hs : I t s) :
      Budget (forIn ys s step) (fun r => r=ys.foldl f s ∧ I xs.length r) (ys.length*c) := by
    induction ys generalizing s t with
    | nil =>
      simp only [List.length_nil,Nat.zero_mul,List.forIn_nil,List.foldl_nil] at *
      apply bPure
      exact ⟨rfl,by simpa [←hl] using hs⟩
    | cons x ys ih =>
      rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm _ c]
      apply bBind (hstep x (hy (by simp)) t (by simp at hl;omega) s hs)
      intro r hr
      rw [hr.1]
      exact ih (fun k hk => hy (by simp [hk])) (t+1) (by simp at hl;omega) _ hr.2
  exact aux xs (fun _ h => h) 0 (by simp) a h0

def put {K V : Type} (ix : K → ℕ) (val : K → V) (gain : K → ℤ) (st : ℤ × Array V) (k : K) :
    ℤ × Array V := (st.1 + gain k,st.2.set! (ix k) (val k))

theorem put_spec {K V : Type} (xs : List K) (ix : K → ℕ) (val : K → V) (gain : K → ℤ)
    (a : ℤ × Array V) (hbound : ∀ x∈xs, ix x < a.2.size)
    (compat : ∀ x∈xs, ∀ y∈xs, ix x=ix y → val x=val y) :
    let out := xs.foldl (put ix val gain) a
    out.2.size=a.2.size ∧ out.1=a.1+(xs.map gain).sum ∧
    (∀ x∈xs, out.2[ix x]? = some (val x)) ∧
    (∀ j, (∀ x∈xs, ix x ≠ j) → out.2[j]?=a.2[j]?) := by
  have he (ys : List K) (st : ℤ × Array V) :
      (ys.foldl (put ix val gain) st).swap=ys.foldl (writeAt ix val gain) st.swap := by
    induction ys generalizing st with
    | nil => rfl
    | cons x ys ih => exact ih (put _ _ _ _ _)
  simpa only [←he,Prod.fst_swap,Prod.snd_swap] using writes_spec xs ix val gain a.swap hbound compat
end TableGrid

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel TableGrid Finset CountLayers
namespace LargeDP
abbrev SetM (m : ℕ) := Finset (Fin m)
abbrev Pairs (m : ℕ) := SetM m × SetM m

def idx {m} (k q width : ℕ) (p : Pairs m) := key (k-q) p.1*width+key 0 p.2
noncomputable def stepFn {m} (A B : Tensor m) (v : Fin m) (k q width : ℕ) :=
  put (idx (m:=m) k q width) (fun p => pair A B p.1 p.2) (fun p => gain A B v k q p.1 p.2)

def rowOver (m : ℕ) := 8*(m+1)^3+addressCost m
abbrev mass (m : ℕ) := 2^(termWidth m)
abbrev ROk {m} (k q : ℕ) (I : SetM m) := I.card=q ∧ ∀ i ∈ I, k-q ≤ i.val

theorem row_budget {m} (A B : Tensor m) (hA : ZeroOne A) (hB : ZeroOne B) (v : Fin m)
    (t : Array (Array ℕ)) (ht : ∀ i j, i < m → j ≤ m → ((t[i]?.getD #[])[j]?.getD 0)=i.choose j)
    (k q w nc : ℕ) (prev : Table)
    (hold : (0 < q → ∀ I' J' : SetM m, I'.card=q-1 → J'.card=q-1 → (∀ x ∈ I', k-(q-1) ≤ x.val) →
      prev[key (k-(q-1)) I'*w+key 0 J']?.getD (0,0)=pair A B I' J'))
    (cols : List (SetM m)) (hcols : ∀ J ∈ cols, J.card=q) (I : SetM m) (hi : ROk k q I)
    (b : StepState) (n : ℕ) (hs : b.1.natAbs ≤ n*mass m)
    (hcap : n+cols.length ≤ (m+1)*4^m) :
    Budget (rowStep A B v t k q w nc prev cols I b)
      (fun r => r = .yield (cols.foldl (fun s J => stepFn A B v k q nc s (I,J)) b) ∧
        (cols.foldl (fun s J => stepFn A B v k q nc s (I,J)) b).1.natAbs ≤ (n+cols.length)*mass m)
      (rowOver m + cols.length*entryCost m (uniformWidth m)) := by
  let f := fun (s : StepState) (J : SetM m) => stepFn A B v k q nc s (I,J)
  let P := fun (j : ℕ) (s : StepState) => s.1.natAbs ≤ (n+j)*mass m
  unfold rowStep
  refine bLe (bTick (bBind (w:=cols.length*entryCost m (uniformWidth m)) (rankBudget t (k-q) I ht) ?_)) ?_
  · intro ri hri
    subst ri
    have hloop := countedFold cols (entryStep A B v t k q w nc (key (k-q) I) prev I (I.sort (· ≤ ·)).head?) f P b (entryCost m (uniformWidth m)) (by simpa [P] using hs) (by
      intro J hJ j hj s hsj
      have hu := (Nat.mul_le_mul_right (mass m) (show n+j ≤ (m+1)*4^m by omega)).trans (uniform_bound m)
      have hh := entry_budget A B hA hB v t ht prev w k q nc (key (k-q) I) (uniformWidth m) I J hi.1 (hcols J hJ) hi.2 hold s (hsj.trans hu)
      apply bMap hh
      intro r he
      refine ⟨he,?_⟩
      have hb := gain_bound A B hA hB v k q I J ((hcols J hJ).trans hi.1.symm)
      change (s.1+gain A B v k q I J).natAbs ≤ _
      have h := (Int.natAbs_add_le _ _).trans (Nat.add_le_add hsj hb)
      simpa only [P,Nat.add_assoc] using h.trans_eq (show (n+j)*mass m+mass m=(n+(j+1))*mass m by ring))
    apply bLe (bBind (w:=0) hloop ?_) (by omega)
    intro y hy
    apply bPure
    exact ⟨congrArg ForInStep.yield hy.1,hy.1 ▸ hy.2⟩
  · unfold rowOver; omega

theorem nested_fold {R C S : Type} (rs : List R) (cs : List C) (f : S → R × C → S) (s : S) :
    rs.foldl (fun s r => cs.foldl (fun s c => f s (r,c)) s) s =
    (rs.flatMap (fun r => cs.map (fun c => (r,c)))).foldl f s := by
  induction rs generalizing s with
  | nil => rfl
  | cons r rs ih => simp [List.foldl_append,List.foldl_map,ih]

theorem grid_budget {m} (A B : Tensor m) (hA : ZeroOne A) (hB : ZeroOne B) (v : Fin m)
    (t : Array (Array ℕ)) (ht : ∀ i j, i < m → j ≤ m → ((t[i]?.getD #[])[j]?.getD 0)=i.choose j)
    (k q : ℕ) (hq : q ≤ m) (st : LayerState) (hs : ready A B k q st)
    (rows cols : List (SetM m)) (hr : ∀ I ∈ rows, ROk k q I) (hc : ∀ J ∈ cols, J.card=q)
    (hcells : rows.length*cols.length ≤ 4^m) (nc : ℕ) (start : StepState) (ha : start.1=st.2.2) :
    Budget (forIn rows start (rowStep A B v t k q st.2.1 nc st.1 cols))
      (fun r => r=(rows.flatMap (fun I => cols.map (fun J => (I,J)))).foldl (stepFn A B v k q nc) start ∧
        r.1.natAbs ≤ (q+1)*4^m*mass m)
      (rows.length*(rowOver m+cols.length*entryCost m (uniformWidth m))) := by
  let P := fun (i : ℕ) (s : StepState) => s.1.natAbs ≤ (q*4^m+i*cols.length)*mass m
  let f := fun s I => cols.foldl (fun s J => stepFn A B v k q nc s (I,J)) s
  have ht' := countedFold rows _ f P start (rowOver m+cols.length*entryCost m (uniformWidth m)) (by
    simpa [P,ha] using hs.2) (by
    intro I hI i hi s hsi
    have hlen : i*cols.length+cols.length ≤ rows.length*cols.length := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right cols.length hi
    have hbound := Nat.mul_le_mul_right (4^m) (Nat.succ_le_succ hq)
    rw [Nat.succ_mul,Nat.succ_mul] at hbound
    have hh := row_budget A B hA hB v t ht k q st.2.1 nc st.1 hs.1 cols hc I (hr I hI) s _ hsi (by
      rw [Nat.succ_mul]; omega)
    apply bMap hh
    intro r he
    refine ⟨he.1,?_⟩
    change _ ≤ (q*4^m+(i+1)*cols.length)*mass m
    simpa [Nat.add_mul,Nat.add_assoc] using he.2)
  apply bMap ht'
  intro r hy
  refine ⟨hy.1.trans (nested_fold _ _ _ _),?_⟩
  exact hy.2.trans (Nat.mul_le_mul_right (mass m) (by rw [Nat.add_mul,one_mul];omega))
end LargeDP

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel Finset CountLayers
open scoped BigOperators
namespace LargeDP
def suffixList (m lo : ℕ) := (List.finRange m).filter (fun i => decide (lo ≤ i.val))
theorem suffixList_size (m lo : ℕ) : (suffixList m lo).length=m-lo := by
  classical
  let xs := suffixList m lo
  have hn : xs.Nodup := (List.nodup_finRange m).filter _
  change xs.length=_
  rw [←List.toFinset_card_of_nodup hn]
  by_cases hlo : lo < m
  · let v : Fin m := ⟨lo,hlo⟩
    have he : xs.toFinset=Finset.Ici v := by ext i; simp [xs,suffixList,v,Fin.le_def]
    rw [he,Fin.card_Ici]
  · have he : xs.toFinset=∅ := by
      ext i
      have hi : ¬ (lo ≤ i.val) := by have := i.isLt; omega
      simp [xs,suffixList,hi]
    rw [he]; simp; omega

theorem suffixBudget (m lo : ℕ) : Budget (suffix (m:=m) lo) (·=suffixList m lo) (4*m+1+(m+3)*m) := by
  constructor; intro s; rw [suffix_run]; exact ⟨rfl,by dsimp; omega⟩

def enumCost (m n : ℕ) := (m+4)*(3*(m+1)*n+1)
theorem rowListBudget (m lo q : ℕ) : Budget (chooseSets (suffixList m lo) q)
    (fun rs => rs.Perm ((allowed (m:=m) lo).powersetCard q).toList ∧ rs.length=(m-lo).choose q)
    (enumCost m ((m-lo).choose q)) := by
  constructor; intro s
  have h := chooseSets_spec (suffixList m lo) q s
  have hperm := row_set_perm (m:=m) lo q 0 s
  rw [suffix_run] at hperm
  have hlen := h.1.length_eq
  simp only [List.length_map,List.length_sublistsLen,suffixList_size] at hlen
  refine ⟨⟨hperm,hlen⟩,h.2.trans ?_⟩
  rw [suffixList_size]; unfold enumCost; gcongr; exact Nat.sub_le _ _

theorem colListBudget (m q : ℕ) : Budget (chooseSets (List.finRange m) q)
    (fun cs => cs.Perm ((univ : Finset (Fin m)).powersetCard q).toList ∧ cs.length=m.choose q)
    (enumCost m (m.choose q)) := by
  constructor; intro s
  have h := chooseSets_spec (List.finRange m) q s
  refine ⟨⟨chooseSets_perm_layer _ _,by simpa using h.1.length_eq⟩,?_⟩
  simpa only [List.length_finRange,enumCost] using h.2

theorem layer_gain_sum {m} (A B : Tensor m) (v : Fin m) (k q : ℕ)
    (rows cols : List (Finset (Fin m))) (hr : rows.Perm ((allowed (m:=m) (k-q)).powersetCard q).toList)
    (hc : cols.Perm ((univ : Finset (Fin m)).powersetCard q).toList) :
    ((rows.flatMap (fun I => cols.map (fun J => (I,J)))).map (fun p => gain A B v k q p.1 p.2)).sum
      = layerSum A B v k q := by
  classical
  have H {T : Type} (xs : List T) (f : T → List ℤ) : (xs.flatMap f).sum=(xs.map (fun x => (f x).sum)).sum := by
    induction xs with
    | nil => rfl
    | cons a l ih => simp [ih]
  simp only [List.map_flatMap,List.map_map,Function.comp_def,H]
  unfold layerSum
  rw [(hr.map _).sum_eq]
  simp only [Finset.sum_map_toList]
  apply Finset.sum_congr rfl
  intro I _
  rw [(hc.map _).sum_eq]
  simp only [Finset.sum_map_toList,gain]

theorem entries_bound (m k q : ℕ) : nEntries m k q ≤ 4^m := by
  have ha := (Nat.choose_le_two_pow (m-(k-q)) q).trans (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le _ _))
  have hb := Nat.choose_le_two_pow m q
  exact (Nat.mul_le_mul ha hb).trans_eq (by rw [←mul_pow]; rfl)
end LargeDP

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel TableGrid Finset CountLayers ColexBounds
namespace LargeDP
private theorem price (m nr nc : ℕ) (ha : 0 < nr) (hb : 0 < nc) :
    8*(m+1)^3 + ((4*m+1+(m+3)*m) + (enumCost m nr + (enumCost m nc +
      ((nr*nc+1)*((m+1)^2+1) + nr*(rowOver m+nc*entryCost m (uniformWidth m)))))) ≤ nr*nc*layerRate m := by
  let N := nr*nc
  have h1 : 1 ≤ N := Nat.mul_pos ha hb
  have hr : nr ≤ N := by exact Nat.le_mul_of_pos_right _ hb
  have hc : nc ≤ N := by exact Nat.le_mul_of_pos_left _ ha
  have ea (n : ℕ) (hn : n ≤ N) : enumCost m n ≤ N*((m+4)*(3*(m+1)+1)) := by
    unfold enumCost
    calc
      _ ≤ (m+4)*(3*(m+1)*N+N) := by gcongr
      _ = _ := by ring
  have hp : 8*(m+1)^3+(4*m+1+(m+3)*m) ≤ N*(8*(m+1)^3+(4*m+1+(m+3)*m)) :=
    Nat.le_mul_of_pos_left _ h1
  have hpre : N+1 ≤ N*2 := by omega
  have hzr := Nat.mul_le_mul_right ((m+1)^2+1) hpre
  have hrow := Nat.mul_le_mul_right (rowOver m) hr
  have ht : 8*(m+1)^3+(4*m+1+(m+3)*m) + 2*((m+4)*(3*(m+1)+1))+
      2*((m+1)^2+1)+rowOver m ≤ 1000*(m+1)^5 := by
    unfold rowOver addressCost; ring_nf; omega
  have he := Nat.mul_le_mul_left N ht
  unfold layerRate
  calc
    _ = (8*(m+1)^3+(4*m+1+(m+3)*m)) + enumCost m nr + enumCost m nc + ((N+1)*((m+1)^2+1)) + nr*rowOver m + N*entryCost m (uniformWidth m) := by dsimp [N]; ring
    _ ≤ N*(8*(m+1)^3+(4*m+1+(m+3)*m)) + N*((m+4)*(3*(m+1)+1)) + N*((m+4)*(3*(m+1)+1)) + N*2*((m+1)^2+1) + N*rowOver m + N*entryCost m (uniformWidth m) := by
      exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp (ea nr hr)) (ea nc hc)) hzr) hrow) _
    _ = N*(8*(m+1)^3+(4*m+1+(m+3)*m)+2*((m+4)*(3*(m+1)+1))+2*((m+1)^2+1)+rowOver m) + N*entryCost m (uniformWidth m) := by ring
    _ ≤ _ := (Nat.add_le_add_right he _).trans_eq (by dsimp [N]; ring)

private theorem grid_result {m} (A B : Tensor m) (v : Fin m) (k q : ℕ) (st : LayerState)
    (rows cols : List (SetM m))
    (hr : rows.Perm ((allowed (m:=m) (k-q)).powersetCard q).toList)
    (hc : cols.Perm ((univ : Finset (Fin m)).powersetCard q).toList)
    (out : StepState)
    (hout : out=(rows.flatMap (fun I => cols.map (fun J => (I,J)))).foldl (stepFn A B v k q (m.choose q))
      (st.2.2, Array.replicate (nEntries m k q) (0,0)))
    (hb : out.1.natAbs ≤ (q+1)*4^m*mass m) :
    ready A B k (q+1) (out.2,m.choose q,out.1) ∧ out.1=st.2.2+layerSum A B v k q := by
  classical
  let ps := rows.flatMap (fun I => cols.map (fun J => (I,J)))
  let ix := idx (m:=m) k q (m.choose q)
  let va := fun p : Pairs m => pair A B p.1 p.2
  let gg := fun p : Pairs m => gain A B v k q p.1 p.2
  have hmem (I J : SetM m) : (I,J) ∈ ps ↔ ROk k q I ∧ J.card=q := by
    simp only [ps,List.mem_flatMap,List.mem_map,Prod.mk.injEq]
    have hi : I ∈ rows ↔ ROk k q I := by
      rw [hr.mem_iff,Finset.mem_toList,mem_powersetCard]
      unfold ROk allowed
      simp only [subset_iff,mem_filter,mem_univ,true_and]
      exact and_comm
    have hj : J ∈ cols ↔ J.card=q := by rw [hc.mem_iff]; simp
    aesop
  let start : StepState := (st.2.2, Array.replicate (nEntries m k q) (0,0))
  have hh := put_spec ps ix va gg start (by
    rintro ⟨I,J⟩ h
    obtain ⟨⟨hi,hlo⟩,hj⟩ := (hmem _ _).mp h
    simpa only [start,Array.size_replicate,ix,idx,key,ColexBounds.pairAddress,ColexBounds.digits,nEntries] using pairAddress_lt (I,J) hlo hi hj) (by
    rintro ⟨I,J⟩ hp ⟨I',J'⟩ hp' he
    obtain ⟨⟨hi,hlo⟩,hj⟩ := (hmem _ _).mp hp
    obtain ⟨⟨hi',hlo'⟩,hj'⟩ := (hmem _ _).mp hp'
    exact congrArg va (pairAddress_inj hlo hlo' hi hi' hj hj' he))
  change out = ps.foldl (put ix va gg) start at hout
  rw [←hout] at hh
  obtain ⟨_,hval,ha,_⟩ := hh
  refine ⟨⟨?_,hb⟩,hval.trans (congrArg (st.2.2+·) (layer_gain_sum A B v k q rows cols hr hc))⟩
  simp only [Nat.add_sub_cancel]
  intro _ I J hi hj hlo
  have hw := ha (I,J) ((hmem _ _).mpr ⟨⟨hi,hlo⟩,hj⟩)
  change out.2[ix (I,J)]?.getD (0,0)=va (I,J)
  rw [hw]; rfl

theorem layer_contract {m} (A B : Tensor m) (hA : ZeroOne A) (hB : ZeroOne B) (v : Fin m)
    (k : ℕ) (hk : k ≤ m) : LayerContract A B v k := by
  intro t ht q hq st hs
  let nr := (m-(k-q)).choose q
  let nc := m.choose q
  have hn : 0 < nr := Nat.choose_pos (by omega)
  have hn' : 0 < nc := Nat.choose_pos hq
  unfold layerStep
  simp only [ht _ (Nat.sub_le _ _) _ hq,ht _ le_rfl _ hq]
  refine bLe (bTick (bBind (suffixBudget m (k-q)) (w:=enumCost m nr + (enumCost m nc +
    ((nr*nc+1)*((m+1)^2+1) + nr*(rowOver m+nc*entryCost m (uniformWidth m))))) ?_)) ?_
  · intro xs hx; subst xs
    apply bBind (rowListBudget m (k-q) q)
    intro rows hr
    apply bBind (colListBudget m q)
    intro cols hc
    apply bTick
    let start : StepState := (st.2.2,Array.replicate (nr*nc) (0,0))
    have hgrid := grid_budget A B hA hB v t (fun i j hi hj => ht i hi.le j hj) k q hq st hs rows cols (by
      intro I hi
      have hh := mem_powersetCard.mp (Finset.mem_toList.mp (hr.1.mem_iff.mp hi))
      exact ⟨hh.2,fun x hx => (mem_filter.mp (hh.1 hx)).2⟩) (by
      intro J hj
      exact (mem_powersetCard.mp (Finset.mem_toList.mp (hc.1.mem_iff.mp hj))).2) (by
      rw [hr.2,hc.2]; exact entries_bound m k q) nc start rfl
    rw [hr.2,hc.2] at hgrid
    apply bLe (bBind (w:=0) hgrid ?_) (by simp [nr,nc])
    intro out hout
    apply bPure
    exact grid_result A B v k q st rows cols hr.1 hc.1 out hout.1 hout.2
  · exact price m nr nc hn hn'
end LargeDP

end

section
open BipHamCount.Deterministic
open scoped BigOperators

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ v : Fin m,
          ((largeTerms m A B v (kOf m)).run 0).1 = sigmaLarge A B v (kOf m) ∧
          (((largeTerms m A B v (kOf m)).run 0).2 : ℝ) ≤ 
            C * ((m : ℝ)+1)^c * Real.exp (2*m*Real.binEntropy alpha) := by
  apply LargeDP.from_layer_contract
  intro m A B hA hB v
  exact LargeDP.layer_contract A B hA hB v _ (by unfold kOf; omega)

end
