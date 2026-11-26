-- Prove2me | solution 1 for BipHamCount.Deterministic.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T11:33:37.043795+00:00
-- url     : https://prove2.me/submissions/8568e95f-993e-43eb-a43a-b703be29c0c1

import Mathlib
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Definitions.Def_BipHamCount_Deterministic_Programs
import Definitions.Def_BipHamCount_Deterministic_Core
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Definitions.Def_CapacitatedAssort_General_Work
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size
import Theorems.Thm_BipHamCount_Deterministic_proposition_4_1
import Theorems.Thm_BipHamCount_Deterministic_proposition_4_2
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.Lemmas
import Theorems.Thm_BipHamCount_Deterministic_base_comparison
import Theorems.Thm_BipHamCount_Deterministic_lemma_3_2
import Mathlib.Algebra.Order.Floor.Ring

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
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel
namespace BipHamFront
abbrev VertexSides (n : ℕ) := Array (Fin n) × Array (Fin n)
abbrev Buffers := Array (Array ℤ) × Array (Array ℤ)
abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℤ

def splitSides {n} (c : Fin n → Bool) : Work (VertexSides n) := do
  let mut left : Array (Fin n) := #[]
  let mut right : Array (Fin n) := #[]
  charge (4*n+1)
  for i in List.finRange n do
    charge 3
    if c i then right := right.push i else left := left.push i
  return (left,right)

def buildBuffers {n} (g : Fin n → Fin n → Bool) (base : Fin n) (left right : Array (Fin n)) : Work Buffers := do
  let m := left.size
  let mut aa : Array (Array ℤ) := #[]
  let mut bb : Array (Array ℤ) := #[]
  charge (4*m+1)
  for i in List.finRange m do
    let mut a := #[]
    let mut b := #[]
    charge (4*m+1)
    for j in List.finRange m do
      charge 10
      let u := left[i.val]?.getD base
      let w := right[j.val]?.getD base
      a := a.push (if g u w then (1 : ℤ) else 0)
      b := b.push (if g w u then (1 : ℤ) else 0)
    charge 2
    aa := aa.push a
    bb := bb.push b
  return (aa,bb)

def readA {m} (ab : Buffers) : Mat m := fun i j => ((ab.1[i.val]?.getD #[])[j.val]?).getD 0
def readB {m} (ab : Buffers) : Mat m := fun j i => ((ab.2[i.val]?.getD #[])[j.val]?).getD 0

def balanced {m} (A B : Mat m) (hm : 0 < m) : Work ℕ := do
  charge (8*(m+1)^3)
  let v : Fin m := ⟨0,hm⟩
  let k := kOf m
  let large ← largeTerms m A B v k
  let small ← smallTerms m A B v k
  let z ← zadd large small
  let _ ← zcmp z
  charge (Nat.size z.natAbs+1)
  return z.toNat

def afterColor {n} (g : Fin n → Fin n → Bool) (hn : 0 < n) (c : Fin n → Bool) : Work ℕ := do
  let (left,right) ← splitSides c
  charge (Nat.size n+3)
  if left.size ≠ right.size then return 0
  if hm : 0 < left.size then
    let ab ← buildBuffers g ⟨0,hn⟩ left right
    balanced (readA ab) (readB ab) hm
  else return 0

def program {n} (g : Fin n → Fin n → Bool) : Work ℕ := do
  charge (Nat.size n+2)
  if hn : 0 < n then
    let col ← twoColor n g
    match col with
    | none => return 0
    | some c => afterColor g hn c
  else return 0

theorem factor {n} (g : Fin n → Fin n → Bool) : countHamCycles n g = program g := by rfl
end BipHamFront

end

section
open BipHamCount.Deterministic Equiv
namespace BipHamGraph

private theorem cycle_transport {V W : Type*} (e : V ≃ W) (p : Equiv.Perm V) (h : p.IsCycle) :
    (e.permCongr p).IsCycle := by
  obtain ⟨x,hx,hs⟩ := h
  refine ⟨e x,by simpa [Equiv.permCongr_apply] using hx,?_⟩
  intro y hy
  obtain ⟨y,rfl⟩ := e.surjective y
  obtain ⟨k,hk⟩ := hs (by simpa [Equiv.permCongr_apply] using hy : p y ≠ y)
  refine ⟨k,?_⟩
  change ((e.permCongrHom p)^k) (e x) = e y
  rw [←map_zpow]
  change e ((p ^ k) ((e.symm) (e x))) = _
  simp [hk]

private def ok {V : Type*} [Fintype V] [DecidableEq V] (adj : V → V → Bool) (p : Equiv.Perm V) :=
  p.IsCycle ∧ p.support=Finset.univ ∧ ∀ x, adj x (p x)=true

private theorem forward {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (f : W → W → Bool) (h : ∀ x y, f (e x) (e y)=g x y)
    (p : Equiv.Perm V) (hp : ok g p) : ok f (e.permCongr p) := by
  refine ⟨cycle_transport e p hp.1,?_,?_⟩
  · apply Finset.eq_univ_of_forall
    intro z; obtain ⟨x,rfl⟩ := e.surjective z
    have hx : x ∈ p.support := hp.2.1 ▸ Finset.mem_univ _
    simpa [Equiv.Perm.mem_support,Equiv.permCongr_apply] using hx
  · intro z; obtain ⟨x,rfl⟩ := e.surjective z
    simpa [Equiv.permCongr_apply,h] using hp.2.2 x

theorem hamCount_congr {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (e : V ≃ W) (g : V → V → Bool) (f : W → W → Bool) (h : ∀ x y, f (e x) (e y)=g x y) :
    hamCount g = hamCount f := by
  classical
  let P := (Finset.univ : Finset (Equiv.Perm V)).filter (ok g)
  let Q := (Finset.univ : Finset (Equiv.Perm W)).filter (ok f)
  have htV : hamCount g=P.card := by unfold hamCount; congr 1; ext; simp [P,ok]
  have htW : hamCount f=Q.card := by unfold hamCount; congr 1; ext; simp [Q,ok]
  rw [htV,htW]
  have eq : P.map e.permCongr.toEmbedding = Q := by
    ext z; obtain ⟨p,rfl⟩ := e.permCongr.surjective z
    simp only [Finset.mem_map_equiv,P,Q,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    constructor
    · exact forward e g f h p
    · intro hp
      have he := forward e.symm f g (fun x y => by simpa using (h (e.symm x) (e.symm y)).symm) _ hp
      simpa [←Equiv.permCongr_symm] using he
  rw [←eq,Finset.card_map]

theorem hamCount_unbalanced {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V → Bool) (c : V → Bool) (hc : ∀ i j, g i j=true → c i ≠ c j)
    (hn : (Finset.univ.filter (fun i => c i=false)).card ≠ (Finset.univ.filter (fun i => c i=true)).card) :
    hamCount g = 0 := by
  classical
  unfold hamCount
  apply Finset.card_filter_eq_zero_iff.mpr
  intro p hp hg
  apply hn
  let F := Finset.univ.filter (fun i => c i=false)
  let T := Finset.univ.filter (fun i => c i=true)
  have hs (i : V) := hc i (p i) (hg.2.2 i)
  have he : F.map p.toEmbedding = T := by
    ext j; obtain ⟨i,rfl⟩ := p.surjective j
    simp only [F,T,Finset.mem_map_equiv,Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply]
    have hh := hs i
    cases hi : c i <;> cases hj : c (p i) <;> simp_all
  rw [←Finset.card_map (f:=p.toEmbedding) (s:=F),he]
end BipHamGraph

end

section
namespace BipHamGraph
open BipHamCount.Deterministic

theorem balanced_sides {V : Type*} [Fintype V] [DecidableEq V]
    (g : V → V → Bool) (c : V → Bool) (hc : ∀ i j, g i j=true → c i ≠ c j)
    (m : ℕ) (left right : Fin m → V) (hl : Function.Injective left) (hr : Function.Injective right)
    (hcl : ∀ v, (∃ i, left i=v) ↔ c v=false) (hcr : ∀ v, (∃ i, right i=v) ↔ c v=true) :
    let A : Matrix (Fin m) (Fin m) ℤ := fun i j => if g (left i) (right j) then 1 else 0
    let B : Matrix (Fin m) (Fin m) ℤ := fun j i => if g (right j) (left i) then 1 else 0
    hamCount g=hamCount (bipDigraph A B) := by
  let e' := Sum.elim left right
  have lcol (i) := (hcl _).mp ⟨i,rfl⟩
  have rcol (j) := (hcr _).mp ⟨j,rfl⟩
  let e : (Fin m ⊕ Fin m) ≃ V := Equiv.ofBijective e' ⟨by
    intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl (hl h)
      | inr j => have he : left i=right j := h; have hh := lcol i; rw [he,rcol] at hh; contradiction
    | inr i =>
      cases y with
      | inl j => have he : right i=left j := h; have hh := rcol i; rw [he,lcol] at hh; contradiction
      | inr j => exact congrArg Sum.inr (hr h),by
    intro v; cases h : c v with
    | false => obtain ⟨i,hi⟩ := (hcl _).mpr h; exact ⟨.inl i,hi⟩
    | true => obtain ⟨i,hi⟩ := (hcr _).mpr h; exact ⟨.inr i,hi⟩⟩
  dsimp only
  symm
  apply hamCount_congr e
  rintro (i|i) (j|j)
  · change g (left i) (left j) = false
    cases h : g (left i) (left j)
    · rfl
    · exact False.elim ((hc _ _ h) ((lcol i).trans (lcol j).symm))
  · change g (left i) (right j) = decide ((if g (left i) (right j) then 1 else 0 : ℤ)=1)
    cases g (left i) (right j) <;> decide
  · change g (right i) (left j) = decide ((if g (right i) (left j) then 1 else 0 : ℤ)=1)
    cases g (right i) (left j) <;> decide
  · change g (right i) (right j) = false
    cases h : g (right i) (right j)
    · rfl
    · exact False.elim ((hc _ _ h) ((rcol i).trans (rcol j).symm))

theorem side_length {V : Type*} [Fintype V] [DecidableEq V] (l : List V) (hn : l.Nodup) (c : V → Bool) (b : Bool)
    (hm : ∀ v, v ∈ l ↔ c v=b) : l.length=(Finset.univ.filter (fun v => c v=b)).card := by
  rw [←List.toFinset_card_of_nodup hn]
  congr 1
  ext v; simp [hm]

end BipHamGraph

end

section
namespace BipHamGraph
open BipHamCount.Deterministic

def side (n : ℕ) (c : Fin n → Bool) (b : Bool) := (List.finRange n).filter (fun i => decide (c i=b))

theorem color_reduction (n : ℕ) (g : Fin n → Fin n → Bool) (c : Fin n → Bool)
    (hc : ∀ i j, g i j=true → c i ≠ c j) :
    let L := side n c false
    let R := side n c true
    if h : L.length=R.length then
      let f := L.get
      let t := fun i : Fin L.length => R.get (Fin.cast h i)
      let A : Matrix (Fin L.length) (Fin L.length) ℤ := fun i j => if g (f i) (t j) then 1 else 0
      let B : Matrix (Fin L.length) (Fin L.length) ℤ := fun j i => if g (t j) (f i) then 1 else 0
      hamCount g=hamCount (bipDigraph A B)
    else hamCount g=0 := by
  dsimp only
  have sm (b : Bool) (v : Fin n) : v ∈ side n c b ↔ c v=b := by simp [side]
  have sn (b : Bool) : (side n c b).Nodup := (List.nodup_finRange n).filter _
  split
  next h =>
    apply balanced_sides g c hc _ _ _ (sn false).injective_get
      ((sn true).injective_get.comp (Fin.cast_injective h))
    · intro v; rw [← sm false]
      exact List.mem_iff_get.symm
    · intro v; rw [← sm true]
      constructor
      · rintro ⟨i,hi⟩
        exact List.mem_iff_get.mpr ⟨_,hi⟩
      · intro hv
        obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
        exact ⟨Fin.cast h.symm j,by simpa using hj⟩
  next h =>
    apply hamCount_unbalanced g c hc
    rw [←side_length _ (sn false) c false (sm false),←side_length _ (sn true) c true (sm true)]
    exact h
end BipHamGraph

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel BipHamGraph
namespace BipHamFront
private theorem splitLoop {n} (c : Fin n → Bool) (L : List (Fin n)) (a b : Array (Fin n)) :
    Budget (forIn L (a,b) (fun i (s : VertexSides n) => do
      charge 3
      if c i then return .yield (s.1,s.2.push i) else return .yield (s.1.push i,s.2)))
      (fun r => r.1.toList=a.toList++L.filter (fun i => decide (c i=false)) ∧ 
        r.2.toList=b.toList++L.filter (fun i => decide (c i=true))) (L.length*3) := by
  induction L generalizing a b with
  | nil =>
    simp only [List.forIn_nil,List.filter_nil,List.append_nil,List.length_nil,Nat.zero_mul]
    exact bPure ⟨rfl,rfl⟩
  | cons i l ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm _ 3]
    cases h : c i with
    | true =>
      exact bWeaken (bTick (ih a (b.push i))) (by intro r hr; simpa [h,List.append_assoc] using hr) le_rfl
    | false =>
      exact bWeaken (bTick (ih (a.push i) b)) (by intro r hr; simpa [h,List.append_assoc] using hr) le_rfl

theorem split_budget {n} (c : Fin n → Bool) : Budget (splitSides c)
    (fun r => r.1.toList=side n c false ∧ r.2.toList=side n c true) (4*n+1+n*3) := by
  unfold splitSides
  apply bTick
  refine bLe (bBind (w:=0) (splitLoop c (List.finRange n) #[] #[]) ?_) (by simp)
  intro r hr
  exact bPure (by simpa [side] using hr)

private theorem doublePush {α β γ : Type} (L : List α) (f : α → β) (g : α → γ) (a : Array β) (b : Array γ)
    (step : α → Array β × Array γ → Work (ForInStep (Array β × Array γ))) (k : ℕ)
    (hs : ∀ i s, Budget (step i s) (· = .yield (s.1.push (f i),s.2.push (g i))) k) :
    Budget (forIn L (a,b) step) (fun out => out.1.toList=a.toList++L.map f ∧ out.2.toList=b.toList++L.map g)
      (L.length*k) := by
  induction L generalizing a b with
  | nil => simp only [List.forIn_nil,List.map_nil,List.append_nil,List.length_nil,Nat.zero_mul]; exact bPure ⟨rfl,rfl⟩
  | cons i L ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm _ k]
    apply bBind (hs i (a,b))
    intro r hr; subst r
    apply bMap (ih _ _)
    intro out h
    simpa [List.append_assoc] using h

private abbrev AEntry {n m : ℕ} (g : Fin n → Fin n → Bool) (d : Fin n)
    (left right : Array (Fin n)) (i j : Fin m) : ℤ :=
  if g (left[i.val]?.getD d) (right[j.val]?.getD d) then 1 else 0
private abbrev BEntry {n m : ℕ} (g : Fin n → Fin n → Bool) (d : Fin n)
    (left right : Array (Fin n)) (i j : Fin m) : ℤ :=
  if g (right[j.val]?.getD d) (left[i.val]?.getD d) then 1 else 0

def bufferWork (m : ℕ) := 4*m+1 + m*(4*m+1 + m*10+2)

theorem buffers_budget {n} (g : Fin n → Fin n → Bool) (d : Fin n) (left right : Array (Fin n)) :
    let m := left.size
    Budget (buildBuffers g d left right) (fun o =>
      (readA o : Mat m) = AEntry g d left right ∧ (readB o : Mat m) = fun j i => BEntry g d left right i j)
      (bufferWork m) := by
  let m := left.size
  let as := fun i : Fin m => ((List.finRange m).map (AEntry g d left right i)).toArray
  let bs := fun i : Fin m => ((List.finRange m).map (BEntry g d left right i)).toArray
  dsimp only
  unfold buildBuffers
  apply bTick
  refine bLe (bBind (w:=0) (doublePush (List.finRange m) as bs #[] #[] _ (4*m+1+m*10+2) ?_) ?_) (by simp [bufferWork,m])
  · intro i s
    refine bLe (bTick (bBind (w:=2) (doublePush (List.finRange m) (AEntry g d left right i) (BEntry g d left right i)
      #[] #[] _ 10 ?_) ?_)) (by simp [m];omega)
    · intro j z; exact ⟨fun s => ⟨rfl,le_rfl⟩⟩
    · intro z hz
      constructor; intro counter; refine ⟨?_,le_rfl⟩
      change ForInStep.yield (s.1.push z.1,s.2.push z.2) = _
      have ha : z.1=as i := by apply Array.toList_inj.mp;simpa [as] using hz.1
      have hb : z.2=bs i := by apply Array.toList_inj.mp;simpa [bs] using hz.2
      rw [ha,hb]
  · intro r hr
    apply bPure
    have ha : r.1=((List.finRange m).map as).toArray := by apply Array.toList_inj.mp; simpa using hr.1
    have hb : r.2=((List.finRange m).map bs).toArray := by apply Array.toList_inj.mp; simpa using hr.2
    constructor
    · ext i j
      simp [readA,ha,as,m,i.isLt,j.isLt]
    · ext j i
      simp [readB,hb,bs,m,i.isLt,j.isLt]
end BipHamFront

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel BipHamGraph
namespace BipHamFront

def frontWork (n : ℕ) := (4*n+1+n*3)+(n.size+3)+bufferWork n

theorem after_color_budget {n} (g : Fin n → Fin n → Bool) (hn : 0 < n) (c : Fin n → Bool)
    (hc : ∀ i j, g i j=true → c i ≠ c j) (t : ℕ)
    (core : ∀ m, n=m+m → ∀ (A B : Mat m) (hm : 0 < m), ZeroOne A → ZeroOne B →
      Budget (balanced A B hm) (·=hamCount (bipDigraph A B)) t) :
    Budget (afterColor g hn c) (· = hamCount g) (frontWork n+t) := by
  let L := side n c false
  let R := side n c true
  have hnLR : n=L.length+R.length := by
    have h := List.length_eq_length_filter_add (l:=List.finRange n) c
    simpa [L,R,side,Nat.add_comm] using h
  have hspec := color_reduction n g c hc
  unfold afterColor
  refine bLe (bBind (w:=n.size+3+bufferWork n+t) (split_budget c) ?_) (by unfold frontWork;omega)
  rintro ⟨left,right⟩ hs
  have hl : left.toList=L := hs.1
  have hr : right.toList=R := hs.2
  have hL : left.size=L.length := by simpa using congrArg List.length hl
  have hR : right.size=R.length := by simpa using congrArg List.length hr
  refine bLe (bTick (c:=bufferWork n+t) ?_) (by omega)
  by_cases he : left.size=right.size
  · have he' : L.length=R.length := by omega
    have hn2 : n=left.size+left.size := by omega
    have hm : 0 < left.size := by omega
    simp only [if_neg (not_not.mpr he),dif_pos hm]
    set m := left.size
    have hle : m ≤ n := by dsimp [m];omega
    have hmono : bufferWork m ≤ bufferWork n := by unfold bufferWork; gcongr
    refine bLe (bBind (w:=t) (buffers_budget g ⟨0,hn⟩ left right) ?_) (Nat.add_le_add_right hmono t)
    intro ab hab
    let A := (readA ab : Mat m)
    let B := (readB ab : Mat m)
    let f := fun i : Fin m => left[i.val]?.getD ⟨0,hn⟩
    let r := fun i : Fin m => right[i.val]?.getD ⟨0,hn⟩
    have Aeq (i j : Fin m) : A i j=(if g (f i) (r j) then 1 else 0) := by rw [show A=readA ab from rfl,hab.1]
    have Beq (i j : Fin m) : B j i=(if g (r j) (f i) then 1 else 0) := by rw [show B=readB ab from rfl,hab.2]
    have ha : ZeroOne A := fun i j => by rw [Aeq];split<;>simp
    have hb : ZeroOne B := fun j i => by rw [Beq];split<;>simp
    apply bMap (core m hn2 A B hm ha hb)
    intro x hx; rw [hx]
    have fg (i : Fin m) : f i=L.get (Fin.cast hL i) := by
      simp only [f,←Array.getElem?_toList,hl,List.get_eq_getElem]
      have hi : i.val < L.length := i.isLt.trans_eq hL
      simp [hi]
    have rg (i : Fin m) : r i=R.get (Fin.cast (hL.trans he') i) := by
      simp only [r,←Array.getElem?_toList,hr,List.get_eq_getElem]
      have hi : i.val < R.length := i.isLt.trans_eq (hL.trans he')
      simp [hi]
    have injf : Function.Injective f := by
      intro i j h; rw [fg,fg] at h
      apply Fin.cast_injective hL
      exact ((List.nodup_finRange n).filter _).injective_get h
    have injr : Function.Injective r := by
      intro i j h; rw [rg,rg] at h
      apply Fin.cast_injective (hL.trans he')
      exact ((List.nodup_finRange n).filter _).injective_get h
    have hf (v : Fin n) : (∃ i, f i=v) ↔ c v=false := by
      rw [←show v ∈ L ↔ c v=false by simp [L,side],List.mem_iff_get]
      exact ⟨fun ⟨i,h⟩=>⟨_,(fg i).symm.trans h⟩,fun ⟨j,h⟩=>⟨Fin.cast hL.symm j,by rw [fg];simpa using h⟩⟩
    have hr' (v : Fin n) : (∃ i, r i=v) ↔ c v=true := by
      rw [←show v ∈ R ↔ c v=true by simp [R,side],List.mem_iff_get]
      exact ⟨fun ⟨i,h⟩=>⟨_,(rg i).symm.trans h⟩,fun ⟨j,h⟩=>⟨Fin.cast (hL.trans he').symm j,by rw [rg];simpa using h⟩⟩
    have hAB := balanced_sides g c hc m f r injf injr hf hr'
    have hA : A=fun i j => if g (f i) (r j) then 1 else 0 := funext fun i => funext fun j => Aeq i j
    have hB : B=fun j i => if g (r j) (f i) then 1 else 0 := funext fun j => funext fun i => Beq i j
    simpa only [hA,hB] using hAB.symm
  · have hu : L.length ≠ R.length := by omega
    have zero : hamCount g=0 := by
      simpa [show (side n c false).length ≠ (side n c true).length from hu] using hspec
    simp only [if_pos he]
    exact bLe (bPure zero.symm) (Nat.zero_le _)

end BipHamFront

end

section
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

end

section
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

end

section
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

end

section
open BipHamCount.Deterministic WorkCalc CapacitatedAssort.General
namespace BipHamFront
private theorem fixedSign (i : ℕ) : Fixed (paritySign i) := WorkCalc.bind (tick _) (fun _ => ret _)
private theorem fixedAdd (a b : ℤ) : Fixed (zadd a b) := WorkCalc.bind (tick _) (fun _ => ret _)
private theorem fixedMul (a b : ℤ) : Fixed (zmul a b) := WorkCalc.bind (tick _) (fun _ => ret _)
private theorem fixedNeg (a : ℤ) : Fixed (zsub 0 a) := WorkCalc.bind (tick _) (fun _ => ret _)
private theorem chooseFixed {m} (is : List (Fin m)) (q : ℕ) : Fixed (chooseSets is q) := by
  induction is generalizing q with
  | nil => cases q <;> rw [chooseSets] <;> repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
  | cons i is ih =>
    cases q <;> rw [chooseSets] <;> repeat' first | (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split) | with_reducible exact ih _
private theorem labelsFixed {m} (is : List (Fin m)) : Fixed (labelPairs is) := by
  induction is with
  | nil => rw [labelPairs];repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
  | cons i is ih => rw [labelPairs];repeat' first | (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split) | assumption
private theorem suffixFixed (m k : ℕ) : Fixed (suffix (m:=m) k) := by unfold suffix;repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
private theorem binomFixed (m : ℕ) : Fixed (binomTable m) := by unfold binomTable;repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
private theorem colexFixed {m} (t : Array (Array ℕ)) (lo : ℕ) (I : Finset (Fin m)) : Fixed (colex t lo I) := by
  unfold colex;repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)
private theorem tableFixed (m w i j : ℕ) (t : Array (ℤ × ℤ)) : Fixed (tableRead m w i j t) :=
  WorkCalc.bind (tick _) (fun _ => ret _)
private theorem bufferFixed {m} (M : Matrix (Fin m) (Fin m) ℤ) (I J : Finset (Fin m)) :
    Fixed (minorBuffer M I J) := by unfold minorBuffer;repeat' (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split)

set_option maxHeartbeats 2000000 in
private theorem summandFixed {m} (A B : Matrix (Fin m) (Fin m) ℤ) (I J : Finset (Fin m)) (a b : ℤ) :
    Fixed (largeSummand A B I J a b) := by
  have hb := berkowitz_fixed intOps fixedAdd fixedMul fixedNeg
  unfold largeSummand
  repeat' first | (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split) | with_reducible exact bufferFixed _ _ _ | with_reducible exact hb _ _
                | with_reducible exact fixedSign _ | with_reducible exact fixedMul _ _

set_option maxHeartbeats 2000000 in
theorem large_fixed {m} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    Fixed (largeTerms m A B v k) := by
  unfold largeTerms
  repeat' first | (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split) | with_reducible exact binomFixed _ | with_reducible exact suffixFixed _ _
                | with_reducible exact chooseFixed _ _ | with_reducible exact colexFixed _ _ _
                | with_reducible exact tableFixed _ _ _ _ _ | with_reducible exact summandFixed _ _ _ _ _ _
                | with_reducible exact fixedAdd _ _ | with_reducible exact fixedMul _ _ | split

set_option maxHeartbeats 1000000 in
theorem small_fixed {m} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (k : ℕ) :
    Fixed (smallTerms m A B v k) := by
  unfold smallTerms
  repeat' first | (first | with_reducible exact WorkCalc.tick _ | with_reducible exact WorkCalc.ret _ | with_reducible refine WorkCalc.list _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.array _ _ _ (fun x y => ?_) | with_reducible refine WorkCalc.bind ?_ (fun x => ?_) | split) | with_reducible exact suffixFixed _ _ | with_reducible exact chooseFixed _ _
                | with_reducible exact labelsFixed _ | with_reducible exact computeF_fixed m A B v k _ _
                | with_reducible exact fixedSign _ | with_reducible exact fixedMul _ _ | with_reducible exact fixedAdd _ _

end BipHamFront

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


open Finset BipHamCount.Deterministic
open scoped BigOperators

namespace BipHamFront
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

def bitWidth (m : ℕ) := 4*m*m + 2*m

private theorem term_abs {m} (A B : Matrix (Fin m) (Fin m) ℤ) (ha : ZeroOne A) (hb : ZeroOne B)
    (I J : Finset (Fin m)) : (sigmaTerm A B I J).natAbs ≤ ((2^(m*m))^4) := by
  have hf : m.factorial ≤ 2^(m*m) := Nat.factorial_le_pow m |>.trans
    ((Nat.pow_le_pow_left Nat.lt_two_pow_self.le m).trans_eq (pow_mul 2 m m).symm)
  unfold sigmaTerm
  simp only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,one_pow,one_mul]
  calc _ ≤ 2^(m*m)*2^(m*m)*2^(m*m)*2^(m*m) := by
          gcongr
          · exact LargeDP.permMinor_power A ha _ _
          · exact LargeDP.permMinor_power B hb _ _
          · exact (abs_minor A ha _ _).trans hf
          · exact (abs_minor B hb _ _).trans hf
       _ = _ := by ring

theorem sums_abs {m} (A B : Matrix (Fin m) (Fin m) ℤ) (ha : ZeroOne A) (hb : ZeroOne B)
    (v : Fin m) (k : ℕ) : (sigmaLarge A B v k).natAbs ≤ 2^(bitWidth m) ∧ 
      (sigmaSmall A B v k).natAbs ≤ 2^(bitWidth m) := by
  have fixed (is : Finset (Finset (Fin m))) (js : Finset (Fin m) → Finset (Finset (Fin m))) :
      (∑ i ∈ is, ∑ j ∈ js i, sigmaTerm A B i j).natAbs ≤ 2^(bitWidth m) := by
    let t := (2^(m*m))^4
    have setSize (s : Finset (Finset (Fin m))) : s.card ≤ 2^m := by simpa using card_le_univ s
    have inner (i) : (∑ j ∈ js i,sigmaTerm A B i j).natAbs ≤ 2^m*t :=
      (abs_sum_bound (js i) _ t (fun j _ => term_abs A B ha hb i j)).trans (Nat.mul_le_mul_right _ (setSize _))
    apply (abs_sum_bound _ _ _ (fun i _ => inner i)).trans
    calc _ ≤ 2^m*(2^m*t) := Nat.mul_le_mul_right _ (setSize _)
         _ = _ := by dsimp [bitWidth,t]; rw [←pow_mul,←pow_add,←pow_add];congr 1;ring
  exact ⟨fixed _ _, fixed _ _⟩
end BipHamFront

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel
namespace BipHamFront
def tailWork (m : ℕ) := 8*(m+1)^3+(2*bitWidth m+3)^2+2*(bitWidth m+3)

theorem balanced_budget {m} (A B : Mat m) (hA : ZeroOne A) (hB : ZeroOne B) (hm : 0 < m)
    (t : ℕ) (v : Fin m) (hv : v=⟨0,hm⟩)
    (hvz : ((largeTerms m A B v (kOf m)).run 0).1+((smallTerms m A B v (kOf m)).run 0).1 =
        (hamCount (bipDigraph A B):ℤ))
    (ht : ((largeTerms m A B v (kOf m)).run 0).2+((smallTerms m A B v (kOf m)).run 0).2 ≤ t) :
    Budget (balanced A B hm) (·=hamCount (bipDigraph A B)) (t+tailWork m) := by
  subst v
  let v : Fin m := ⟨0,hm⟩
  let l := largeTerms m A B v (kOf m)
  let r := smallTerms m A B v (kOf m)
  let z := (l.run 0).1+(r.run 0).1
  let w := bitWidth m
  have hab := sums_abs A B hA hB v (kOf m)
  obtain ⟨_,_,_,hL⟩ := proposition_4_1
  obtain ⟨_,_,_,hS⟩ := proposition_4_2
  have leq := (hL m A B hA hB v).1
  have req := (hS m A B hA hB v).1
  have lw : (l.run 0).1.natAbs ≤ 2^w := leq ▸ hab.1
  have rw' : (r.run 0).1.natAbs ≤ 2^w := req ▸ hab.2
  have zw : z.natAbs ≤ 2^(w+1) := by
    apply (Int.natAbs_add_le _ _).trans
    simpa [pow_succ,Nat.mul_two] using Nat.add_le_add lw rw'
  have size (q b : ℕ) (h : q ≤ 2^b) : q.size ≤ b+1 :=
    Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have :=Nat.two_pow_pos b;omega))
  have lbits := size _ _ lw
  have rbits := size _ _ rw'
  have zbits := size _ _ zw
  have a : ((l.run 0).1.natAbs.size+(r.run 0).1.natAbs.size+1)^2 ≤ (2*w+3)^2 :=
    Nat.pow_le_pow_left (by omega) _
  have lv := WorkCalc.eval (large_fixed A B v (kOf m))
  have rv := WorkCalc.eval (small_fixed A B v (kOf m))
  have exactRun (s : ℕ) : (balanced A B hm).run s =
      (z.toNat,s+8*(m+1)^3+(l.run 0).2+(r.run 0).2+
        ((l.run 0).1.natAbs.size+(r.run 0).1.natAbs.size+1)^2+
        (z.natAbs.size+1)+(z.natAbs.size+1)) := by
    let s' := s+8*(m+1)^3
    change (let x := l.run s'; let y := r.run x.2; let a := x.1+y.1;
      (a.toNat,y.2+(x.1.natAbs.size+y.1.natAbs.size+1)^2+(a.natAbs.size+1)+(a.natAbs.size+1))) = _
    have hl : l.run s'=((l.run 0).1,s'+(l.run 0).2) := lv _
    rw [hl]
    have hr : r.run (s'+(l.run 0).2)=((r.run 0).1,(s'+(l.run 0).2)+(r.run 0).2) := rv _
    dsimp only
    rw [hr]
  constructor; intro s
  rw [exactRun]
  have hz : z=(hamCount (bipDigraph A B):ℤ) := hvz
  refine ⟨by simp [hz],?_⟩
  have hh : (l.run 0).2+(r.run 0).2 ≤ t := ht
  change _ ≤ s+(t+tailWork m)
  dsimp only [tailWork]
  change _ ≤ s+(t+(8*(m+1)^3+(2*w+3)^2+2*(w+3)))
  omega
end BipHamFront

end

section

open Filter Asymptotics Real Finset BipHamCount.Deterministic
open scoped BigOperators

private theorem absorb (a b : ℝ) (ha : 0 < a) (hab : a < b) (d : ℕ) :
    ∃ C > (0:ℝ), ∀ n : ℕ, ((n:ℝ)+1)^d*a^n ≤ C*b^n := by
  have h := isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt d
    (by simpa [Real.norm_eq_abs,abs_of_pos ha] using hab : ‖a‖ < b)
  obtain ⟨C,hC,H⟩ := bound_of_isBigO_nat_atTop h.isBigO
  have hb : 0 < b := ha.trans hab
  refine ⟨C*(b/a),by positivity,fun n => ?_⟩
  have hn := H (x:=n+1) (pow_ne_zero _ hb.ne')
  simp only [Nat.cast_add,Nat.cast_one,Real.norm_eq_abs,abs_of_nonneg (by positivity :
    0 ≤ ((n:ℝ)+1)^d*a^(n+1)),abs_of_pos (pow_pos hb _),pow_succ] at hn
  apply le_of_mul_le_mul_right (a:=a) _ ha
  calc
    _ ≤ C*(b^n*b) := by simpa [mul_assoc,abs_of_pos ha,abs_of_pos hb,abs_of_nonneg (by positivity : (0:ℝ) ≤ n+1)] using hn
    _ = _ := by field_simp <;> ring

theorem balanced_core :
    ∃ C > (0:ℝ), ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ),
      ZeroOne A → ZeroOne B → ∀ v : Fin m,
      ((largeTerms m A B v (kOf m)).run 0).1+((smallTerms m A B v (kOf m)).run 0).1 =
        (hamCount (bipDigraph A B):ℤ) ∧ 
      ((((largeTerms m A B v (kOf m)).run 0).2:ℝ)+((smallTerms m A B v (kOf m)).run 0).2) ≤ 
        C*(19526/10000:ℝ)^(2*m) := by
  let H := binEntropy alpha
  let a := exp H
  let a' := exp (H/2)*(3:ℝ)^(alpha/2)
  let b := (19526/10000:ℝ)
  obtain ⟨C,hC,d,hL⟩ := proposition_4_1
  obtain ⟨D,hD,e,hS⟩ := proposition_4_2
  have h1 : 0 < a := exp_pos _
  have h2 : 0 < a' := by dsimp [a']; positivity
  have hb : 0 < b := by norm_num [b]
  obtain ⟨U,hU,hu⟩ := absorb (a^2) (b^2) (by positivity) (pow_lt_pow_left₀ base_comparison.1 h1.le (by decide)) d
  obtain ⟨V,hV,hv⟩ := absorb (a'^2) (b^2) (by positivity) (pow_lt_pow_left₀ base_comparison.2 h2.le (by decide)) e
  refine ⟨C*U+D*V,by positivity,?_⟩
  intro m A B hA hB v
  obtain ⟨vl,tl⟩ := hL m A B hA hB v
  obtain ⟨vs,ts⟩ := hS m A B hA hB v
  constructor
  · rw [vl,vs,←lemma_3_2 m A B hA hB v]
    unfold sigmaLarge sigmaSmall sigma
    rw [←Finset.sum_union]
    · congr 1; ext x; simp only [Finset.mem_union,Finset.mem_filter]; by_cases h : kOf m < x.card <;> simp [h, Nat.le_of_not_gt, Nat.not_le_of_gt]
    · exact Finset.disjoint_left.mpr (fun x h1 h2 =>
        (not_lt_of_ge (Finset.mem_filter.mp h2).2) (Finset.mem_filter.mp h1).2)
  · have hl : exp (2*(m:ℝ)*H)=(a^2)^m := by
      rw [←pow_mul,show 2*(m:ℝ)*H=(2*m:ℕ)*H by push_cast; ring,exp_nat_mul] <;> rfl
    have hs : exp ((m:ℝ)*H)*(3:ℝ)^(alpha*m)=(a'^2)^m := by
      dsimp [a']
      rw [←pow_mul,mul_pow,←exp_nat_mul,←Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
      push_cast; ring_nf
    rw [show exp (2*(m:ℝ)*binEntropy alpha)=(a^2)^m from hl] at tl
    rw [mul_assoc (D*_) _ _,show exp ((m:ℝ)*binEntropy alpha)*(3:ℝ)^(alpha*m)=(a'^2)^m from hs] at ts
    have hL := mul_le_mul_of_nonneg_left (hu m) hC.le
    have hS := mul_le_mul_of_nonneg_left (hv m) hD.le
    change _ ≤ (C*U+D*V)*b^(2*m)
    rw [pow_mul]
    linarith only [tl,ts,hL,hS]

theorem balanced_overhead_cover (b : ℝ) (hb : 1 < b) :
    ∃ C > (0 : ℝ), ∀ n : ℕ, ((n : ℝ)+1)^4 ≤ C*b^n := by
  simpa using absorb 1 b (by norm_num) hb 4

end

section
open BipHamCount.Deterministic CapacitatedAssort.General BerkowitzModel
open Filter Asymptotics
namespace BipHamFront
def graphWork (n : ℕ) := n.size+2+100*(n+1)^3+frontWork n+tailWork n

private theorem work_bound (n : ℕ) : graphWork n ≤ 1000*(n+1)^4 := by
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [graphWork,frontWork,bufferWork,tailWork,bitWidth]
  nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3),Nat.zero_le (n^4)]

private theorem empty_count (g : Fin 0 → Fin 0 → Bool) : hamCount g=0 := by
  classical
  unfold hamCount
  apply Finset.card_filter_eq_zero_iff.mpr
  rintro p _ ⟨⟨i,_⟩,_⟩
  exact i.elim0

theorem from_color_certificate
    (cert : ∀ {n} (g : Fin n → Fin n → Bool), IsBipartiteDigraph g →
      Budget (twoColor n g) (fun o => ∃ f, o=some f ∧ ∀ u w, g u w=true → f u ≠ f w) (100*(n+1)^3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (g : Fin n → Fin n → Bool), IsBipartiteDigraph g →
      ((countHamCycles n g).run 0).1=hamCount g ∧ 
      (((countHamCycles n g).run 0).2:ℝ) ≤ C*(19526/10000:ℝ)^n := by
  let b : ℝ := 19526/10000
  obtain ⟨C,hC,hcore⟩ := balanced_core
  obtain ⟨D,hD,hD'⟩ := balanced_overhead_cover b (by norm_num [b])
  refine ⟨C+1000*D,by positivity,?_⟩
  intro n g hg
  let t := ⌊C*b^n⌋₊
  have hco (m) (he : n=m+m) (A B : Mat m) (hm : 0 < m) (hA : ZeroOne A) (hB : ZeroOne B) :
      Budget (balanced A B hm) (·=hamCount (bipDigraph A B)) (t+tailWork n) := by
    let v : Fin m := ⟨0,hm⟩
    obtain ⟨hv,hw⟩ := hcore m A B hA hB v
    have ht : ((largeTerms m A B v (kOf m)).run 0).2+((smallTerms m A B v (kOf m)).run 0).2 ≤ t := by
      apply Nat.le_floor
      rw [he,←two_mul];simpa [Nat.cast_add,b] using hw
    apply bLe (balanced_budget A B hA hB hm t v rfl hv ht)
    have hm' : m ≤ n := by omega
    unfold tailWork bitWidth;gcongr
  have hp : Budget (countHamCycles n g) (·=hamCount g) (t+graphWork n) := by
    rw [factor,program]
    by_cases hn : 0 < n
    · simp only [dif_pos hn]
      refine bLe (bTick (bBind (w:=frontWork n+(t+tailWork n)) (cert g hg) ?_)) (by unfold graphWork;omega)
      rintro _ ⟨c,rfl,hc⟩
      exact after_color_budget g hn c hc _ hco
    · simp only [dif_neg hn]
      refine bLe (bTick (bPure ?_)) (by unfold graphWork;omega)
      obtain rfl : n=0 := by omega
      exact (empty_count g).symm
  obtain ⟨hval,hw⟩ := hp.run 0
  refine ⟨hval,?_⟩
  simp only [Nat.zero_add] at hw
  have hnw : ((countHamCycles n g).run 0).2 ≤ t+1000*(n+1)^4 := by simpa using hw.trans (Nat.add_le_add_left (work_bound n) t)
  have hx : (t:ℝ) ≤ C*b^n := Nat.floor_le (by dsimp [b];positivity)
  have hy := hD' n
  have hz : (((countHamCycles n g).run 0).2:ℝ) ≤ (t:ℝ)+1000*((n:ℝ)+1)^4 := by exact_mod_cast hnw
  change _ ≤ (C+1000*D)*b^n
  linarith only [hx,hy,hz]
end BipHamFront

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic
namespace ColorDFS
abbrev Colors := Array (Option Bool)
abbrev Outer := Colors × Bool
abbrev St (n : ℕ) := Colors × Bool × List (Fin n)
def readColor {n : ℕ} (colors : Colors) (v : Fin n) : Option Bool := (colors[v.val]?).getD none

def scan {n} (a : Fin n → Fin n → Bool) (u : Fin n) (cu : Bool) (w : Fin n) (s : St n) :
    Work (ForInStep (St n)) := do
  charge 5
  if a u w || a w u then
    match readColor s.1 w with
    | none =>
      charge 3
      return .yield (s.1.set! w.val (some (!cu)), s.2.1, w :: s.2.2)
    | some cw =>
      charge 1
      if cw = cu then return .yield (s.1,false,s.2.2)
      else return .yield (s.1,s.2.1,s.2.2)
  else return .yield (s.1,s.2.1,s.2.2)
def pop {n} (a : Fin n → Fin n → Bool) (_ : ℕ) (s : St n) : Work (ForInStep (St n)) := do
  charge 2
  match s.2.2 with
  | u :: rest =>
    charge 1
    let cu := (readColor s.1 u).getD false
    charge (4*n+1)
    let v ← forIn (List.finRange n) (s.1,s.2.1,rest) (fun w st => scan a u cu w st)
    return .yield (v.1,v.2.1,v.2.2)
  | _ => return .yield (s.1,s.2.1,s.2.2)
def root {n} (a : Fin n → Fin n → Bool) (r : Fin n) (s : Outer) : Work (ForInStep Outer) := do
  charge 3
  if (readColor s.1 r).isNone then
    charge 2
    let cs := s.1.set! r.val (some false)
    charge (4*n+1)
    let v ← forIn (List.range n) (cs,s.2,[r]) (fun j st => pop a j st)
    return .yield (v.1,v.2.1)
  else return .yield (s.1,s.2)
def program {n} (a : Fin n → Fin n → Bool) : Work (Option (Fin n → Bool)) := do
  charge (4*n+1)
  let s ← forIn (List.finRange n) (Array.replicate n none,true) (fun r st => root a r st)
  charge 1
  return if s.2 then some (fun i => (readColor s.1 i).getD false) else none
theorem factor {n} (a : Fin n → Fin n → Bool) : twoColor n a=program a := by
  rfl
end ColorDFS

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic
namespace ColorDFS
def marked {n} (c : Colors) (x : Fin n) := readColor c x ≠ none
def edge {n} (a : Fin n → Fin n → Bool) (u w : Fin n) := a u w = true ∨ a w u = true
def proper {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) := ∀ u w, edge a u w → f u ≠ f w
structure Valid {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) (exc : Fin n → Prop) (s : St n) : Prop where
  size : s.1.size=n
  good : s.2.1=true
  agree : ∀ x : Fin n, marked s.1 x → readColor s.1 x=some (f x)
  distinct : s.2.2.Nodup
  grey : ∀ x : Fin n, x ∈ s.2.2 → marked s.1 x
  closed : ∀ x : Fin n, marked s.1 x → x ∉ s.2.2 → ¬exc x → ∀ y : Fin n, edge a x y → marked s.1 y

def grows {n} (s t : St n) : Prop := ∀ x : Fin n, marked s.1 x → marked t.1 x ∧ (x ∈ t.2.2 ↔ x ∈ s.2.2)
theorem grows_id {n} (s : St n) : grows s s := fun _ h => ⟨h,Iff.rfl⟩
theorem grows_trans {n} {s t z : St n} (h : grows s t) (g : grows t z) : grows s z := by
  intro x hx
  have a := h x hx
  have b := g x a.1
  exact ⟨b.1,b.2.trans a.2⟩
theorem read_set {n} (c : Colors) (sz : c.size=n) (w x : Fin n) (b : Bool) :
    readColor (c.set! w.val (some b)) x = if x=w then some b else readColor c x := by
  by_cases h : x=w
  · subst x; simp [readColor,Array.set!_eq_setIfInBounds,sz,w.isLt]
  · have hn : w.val ≠ x.val := fun e => h (Fin.ext e.symm)
    simp [readColor,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne hn,h]

theorem pushed {n} {a : Fin n → Fin n → Bool} {f : Fin n → Bool} {exc} {s : St n}
    (v : Valid a f exc s) (w : Fin n) (hw : ¬marked s.1 w) :
    let t : St n := (s.1.set! w.val (some (f w)),s.2.1,w::s.2.2)
    Valid a f exc t ∧ grows s t ∧ marked t.1 w := by
  dsimp only
  have rm (x : Fin n) : marked (s.1.set! w.val (some (f w))) x ↔ x=w ∨ marked s.1 x := by
    unfold marked; rw [read_set _ v.size]; by_cases h : x=w <;> simp [h]
  have hne : w ∉ s.2.2 := fun h => hw (v.grey _ h)
  constructor
  · refine ⟨?_,v.good,?_,List.nodup_cons.mpr ⟨hne,v.distinct⟩,?_,?_⟩
    · simp [Array.set!_eq_setIfInBounds,v.size]
    · intro x hx
      rw [read_set _ v.size]
      obtain hx|hx := (rm x).mp hx
      · simp [hx]
      · have hneq : x ≠ w := fun e => hw (e ▸ hx)
        simpa [hneq] using v.agree x hx
    · intro x hx; rcases List.mem_cons.mp hx with rfl|hx
      · exact (rm _).mpr (Or.inl rfl)
      · exact (rm _).mpr (Or.inr (v.grey _ hx))
    · intro x hx hns he y hy
      obtain hx|hx := (rm x).mp hx
      · exact False.elim (hns (List.mem_cons.mpr (Or.inl hx)))
      · exact (rm _).mpr (Or.inr (v.closed x hx (fun h => hns (List.mem_cons.mpr (Or.inr h))) he y hy))
  · refine ⟨?_,(rm _).mpr (Or.inl rfl)⟩
    intro x hx
    have hn : x ≠ w := fun e => hw (e ▸ hx)
    exact ⟨(rm _).mpr (Or.inr hx),by simp [hn]⟩

theorem scan_value {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) (hf : proper a f)
    (exc : Fin n → Prop) (u w : Fin n) (s : St n) (v : Valid a f exc s) :
    Post (scan a u (f u) w s) (Yield (fun t => Valid a f exc t ∧ grows s t ∧ (edge a u w → marked t.1 w))) := by
  constructor; intro z
  by_cases hE : edge a u w
  · have he : (a u w || a w u)=true := by simpa [edge] using hE
    have hd := hf _ _ hE
    by_cases hm : marked s.1 w
    · have hc := v.agree _ hm
      have hn := Ne.symm hd
      simp only [scan,he,if_true,hc,if_neg hn]
      exact ⟨v,grows_id _,fun _ => hm⟩
    · have hc : readColor s.1 w=none := Classical.not_not.mp hm
      have hflip : (!(f u)) = f w := by cases h : f u <;> cases h' : f w <;> simp_all
      obtain ⟨ht,hg,hw⟩ := pushed v w hm
      simp only [scan,he,if_true,hc,hflip]
      exact ⟨ht,hg,fun _ => hw⟩
  · have he : (a u w || a w u)=false := by simpa [edge] using hE
    simp only [scan,he,Bool.false_eq_true,if_false]
    exact ⟨v,grows_id _,fun h => False.elim (hE h)⟩
end ColorDFS

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic
open Finset
namespace ColorDFS
theorem scan_all {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) (hf : proper a f)
    (exc : Fin n → Prop) (u : Fin n) (xs : List (Fin n)) (s : St n) (v : Valid a f exc s) :
    Post (forIn xs s (scan a u (f u))) (fun t => Valid a f exc t ∧ grows s t ∧ 
      ∀ w ∈ xs, edge a u w → marked t.1 w) := by
  induction xs generalizing s with
  | nil => simpa only [List.forIn_nil] using purePost (x:=s) ⟨v,grows_id _,by simp⟩
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (scan_value a f hf exc u x s v)
    intro j hj
    cases j with
    | done _ => exact False.elim hj
    | yield t =>
      obtain ⟨vt,gst,hx⟩ := hj
      apply postMono (ih t vt)
      rintro z ⟨vz,gtz,hw⟩
      refine ⟨vz,grows_trans gst gtz,?_⟩
      intro w h he; rcases List.mem_cons.mp h with rfl|hh
      · exact (gtz _ (hx he)).1
      · exact hw _ hh he

abbrev Full {n} (a : Fin n → Fin n → Bool) (f) := Valid a f (fun _ => False)
def doneSet {n} (s : St n) : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => readColor s.1 x ≠ none ∧ x ∉ s.2.2)
theorem mem_done {n} {s : St n} {x : Fin n} : x ∈ doneSet s ↔ marked s.1 x ∧ x ∉ s.2.2 := by simp only [doneSet, Finset.mem_filter, Finset.mem_univ, true_and, marked]

theorem pop_step {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) (hf : proper a f)
    (s : St n) (v : Full a f s) (j : ℕ) :
    Post (pop a j s) (Yield (fun t => Full a f t ∧ (∀ x : Fin n, marked s.1 x → marked t.1 x) ∧ 
      ((s.2.2=[] ∧ t.2.2=[]) ∨ (s.2.2 ≠ [] ∧ (doneSet s).card < (doneSet t).card)))) := by
  rcases h : s.2.2 with _|⟨u,rest⟩
  · rcases s with ⟨c,b,st⟩
    change st=[] at h
    subst st
    exact tickPost (purePost ⟨v,fun _ => id,Or.inl ⟨rfl,rfl⟩⟩)
  · let r : St n := (s.1,s.2.1,rest)
    have hu : marked s.1 u := v.grey _ (by simp [h])
    have hn : u ∉ rest := (List.nodup_cons.mp (h ▸ v.distinct)).1
    have vr : Valid a f (·=u) r := by
      refine ⟨v.size,v.good,v.agree,(List.nodup_cons.mp (h ▸ v.distinct)).2,?_,?_⟩
      · intro x hx; exact v.grey _ (by rw [h]; exact List.mem_cons_of_mem _ hx)
      · intro x hx hxs hu' y he
        exact v.closed x hx (by rw [h,List.mem_cons]; exact fun hh => hh.elim hu' hxs) (by simp) y he
    simp only [pop,h,v.agree u hu,Option.getD_some]
    apply tickPost
    apply tickPost
    apply tickPost
    apply bindPost (scan_all a f hf (·=u) u (List.finRange n) r vr)
    rintro t ⟨vt,hg,hi⟩
    apply purePost
    change Full a f t ∧ _
    have vt' : Full a f t := by
      refine ⟨vt.size,vt.good,vt.agree,vt.distinct,vt.grey,?_⟩
      intro x hx hxs _ y he
      by_cases hxu : x=u
      · subst x; exact hi _ (by simp) he
      · exact vt.closed _ hx hxs hxu _ he
    refine ⟨vt',fun x hx => (hg x hx).1,Or.inr ⟨by simp [h],Finset.card_lt_card ?_⟩⟩
    refine (Finset.ssubset_iff_of_subset ?_).mpr ?_
    swap
    · refine ⟨u,?_,?_⟩
      · exact mem_done.mpr ⟨(hg u hu).1,fun hm => hn ((hg u hu).2.mp hm)⟩
      · rw [mem_done]; simp [h]
    · intro x hx
      obtain ⟨hc,hxs⟩ := mem_done.mp hx
      exact mem_done.mpr ⟨(hg x hc).1,fun hm => hxs (by have hxr := (hg x hc).2.mp hm; simpa [h, r] using Or.inr (a:=x=u) hxr)⟩
end ColorDFS

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic Finset
namespace ColorDFS
theorem walk {n} (a : Fin n → Fin n → Bool) (f : Fin n → Bool) (hf : proper a f)
    (s : St n) (v : Full a f s) :
    Post (forIn (List.range n) s (pop a))
      (fun t => Full a f t ∧ (∀ x : Fin n, marked s.1 x → marked t.1 x) ∧ t.2.2=[]) := by
  let I := fun (j : ℕ) (t : St n) => Full a f t ∧ (∀ x : Fin n, marked s.1 x → marked t.1 x) ∧ 
      (t.2.2=[] ∨ j ≤ (doneSet t).card)
  apply postMono (rangePost (n:=n) I (b:=s) ?_ ?_)
  · intro t ht
    obtain ⟨vt,mt,alt⟩ := ht
    refine ⟨vt,mt,?_⟩
    rcases alt with h|h
    · exact h
    · have hc := (doneSet t).card_le_univ
      have he : doneSet t=univ := (doneSet t).card_eq_iff_eq_univ.mp (by simpa using Nat.le_antisymm hc (by simpa using h))
      cases hst : t.2.2 with
      | nil => rfl
      | cons u rest =>
        have hdone : u ∈ doneSet t := by simp [he]
        exact False.elim ((mem_done.mp hdone).2 (by simp [hst]))
  · exact ⟨v,fun _ => id,Or.inr (Nat.zero_le _)⟩
  · intro j hj t ht
    obtain ⟨vt,hmt,hj'⟩ := ht
    apply postMono (pop_step a f hf t vt j)
    intro z hz
    cases z with
    | done _ => exact False.elim hz
    | yield z =>
      obtain ⟨vz,hm,hz⟩ := hz
      refine ⟨vz,fun x hx => hm x (hmt x hx),?_⟩
      rcases hz with ⟨_,hz⟩|⟨hne,hz⟩
      · exact Or.inl hz
      · rcases hj' with hnil|hc
        · exact False.elim (hne hnil)
        · exact Or.inr (by omega)
end ColorDFS

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic Finset
namespace ColorDFS
def idle {n} (s : Outer) : St n := (s.1,s.2,[])
def outerOk {n} (a : Fin n → Fin n → Bool) (s : Outer) := ∃ f, proper a f ∧ Full a f (idle s)

private theorem starts {n} {a : Fin n → Fin n → Bool} {s : Outer} (ho : outerOk a s) (r : Fin n)
    (hr : ¬marked s.1 r) : ∃ g, proper a g ∧ g r=false ∧ Full a g (idle s) := by
  classical
  obtain ⟨f,hf,hv⟩ := ho
  by_cases h : f r=false
  · exact ⟨f,hf,h,hv⟩
  let g := fun x => if marked s.1 x then f x else !(f x)
  refine ⟨g,?_,by simp [g,hr,Bool.eq_true_of_not_eq_false h],?_⟩
  · intro x y he
    have hxy : marked s.1 x ↔ marked s.1 y := by
      constructor
      · intro hx; exact hv.closed x hx (by simp [idle]) (by simp) y he
      · intro hy; exact hv.closed y hy (by simp [idle]) (by simp) x (Or.symm he)
    have hn := hf x y he
    by_cases hx : marked s.1 x
    · simp [g,hx,hxy.mp hx,hn]
    · have hy := mt hxy.mpr hx
      simpa [g,hx,hy] using hn
  · exact ⟨hv.size,hv.good,fun x hx => by change marked s.1 x at hx; simpa only [g,if_pos hx] using hv.agree x hx,hv.distinct,hv.grey,hv.closed⟩

theorem root_step {n} (a : Fin n → Fin n → Bool) (s : Outer) (hs : outerOk a s) (r : Fin n) :
    Post (root a r s) (Yield (fun t => outerOk a t ∧ 
      (∀ x : Fin n, marked s.1 x → marked t.1 x) ∧ marked t.1 r)) := by
  by_cases hr : marked s.1 r
  · have hp : (readColor s.1 r).isNone=false := by
      cases h : readColor s.1 r with
      | none => exact False.elim (hr h)
      | some x => rfl
    simp only [root,hp,Bool.false_eq_true,if_false]
    exact tickPost (purePost ⟨hs,fun _ => id,hr⟩)
  · have hp : readColor s.1 r=none := Classical.not_not.mp hr
    obtain ⟨f,hf,hfr,vo⟩ := starts hs r hr
    obtain ⟨vt,hg,hm⟩ := pushed vo r hr
    simp only [hfr] at vt hg hm
    simp only [root,hp,Option.isNone_none,if_true]
    apply tickPost; apply tickPost; apply tickPost
    apply bindPost (walk a f hf _ vt)
    rintro t ⟨vt',hmt,he⟩
    apply purePost
    refine ⟨⟨f,hf,?_⟩,fun x hx => hmt _ ((hg x hx).1),hmt _ hm⟩
    have hst : idle (n:=n) (t.1,t.2.1)=t := by
      rcases t with ⟨z,b,s⟩; simp [idle] at he ⊢; exact he
    rw [hst]; exact vt'

theorem roots {n} (a : Fin n → Fin n → Bool) (s : Outer) (hs : outerOk a s) (xs : List (Fin n)) :
    Post (forIn xs s (root a)) (fun t => outerOk a t ∧ 
      (∀ x : Fin n, marked s.1 x → marked t.1 x) ∧ ∀ x ∈ xs, marked t.1 x) := by
  induction xs generalizing s with
  | nil => simpa only [List.forIn_nil] using purePost (x:=s) ⟨hs,fun _ => id,by simp⟩
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (root_step a s hs x)
    intro j hj
    cases j with
    | done _ => exact False.elim hj
    | yield z =>
      obtain ⟨ho,hg,hx⟩ := hj
      apply postMono (ih z ho)
      rintro t ⟨ht,hm,hw⟩
      refine ⟨ht,fun x hx => hm _ (hg _ hx),?_⟩
      intro w hh
      rcases List.mem_cons.mp hh with rfl|hh
      · exact hm _ hx
      · exact hw _ hh

theorem color_ok {n} (a : Fin n → Fin n → Bool) (ha : IsBipartiteDigraph a) :
    Post (twoColor n a) (fun o => ∃ f, o=some f ∧ ∀ u w, a u w=true → f u ≠ f w) := by
  rw [factor]; unfold program
  apply tickPost
  let z : Outer := (Array.replicate n none,true)
  have hz : outerOk a z := by
    obtain ⟨f,hf⟩ := ha
    refine ⟨f,?_,?_,rfl,?_,List.nodup_nil,by simp [idle],?_⟩
    · intro x y h; exact h.elim (hf x y) (fun hw => (hf y x hw).symm)
    · simp [z,idle]
    · intro x hx
      simp [marked,readColor,idle,z] at hx
    · intro x hx
      simp [marked,readColor,idle,z] at hx
  apply bindPost (roots a z hz (List.finRange n))
  rintro t ⟨⟨f,hf,vt⟩,_,hm⟩
  apply tickPost; apply purePost
  have hh : t.2=true := vt.good
  simp only [hh,if_true,Option.some.injEq]
  refine ⟨f,funext (fun x => ?_),fun u w h => hf _ _ (Or.inl h)⟩
  have he : readColor t.1 x=some (f x) := vt.agree x (hm _ (by simp))
  rw [he]; rfl
end ColorDFS

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic
namespace ColorCost
def Cheap {α : Type} (p : Work α) (c : ℕ) : Prop := ∀ s, (p.run s).2 ≤ s+c
theorem ret {α : Type} (x : α) : Cheap (pure x) 0 := fun _ => le_rfl
theorem bind {α β : Type} {p : Work α} {f : α → Work β} {u v : ℕ}
    (h : Cheap p u) (g : ∀ x, Cheap (f x) v) : Cheap (p >>= f) (u+v) := by
  intro s
  have hi := h s
  have hj := g (p.run s).1 (p.run s).2
  change ((f (p.run s).1).run (p.run s).2).2 ≤ _
  omega
theorem tick {α : Type} {p : Work α} {u v : ℕ} (h : Cheap p v) :
    Cheap (charge u >>= fun _ => p) (u+v) := by
  intro s; change (p.run (s+u)).2 ≤ _; simpa only [Nat.add_assoc] using h (s+u)
theorem raise {α : Type} {p : Work α} {u v : ℕ} (h : Cheap p u) (huv : u ≤ v) : Cheap p v :=
  fun s => (h s).trans (Nat.add_le_add_left huv s)
theorem list {R S : Type} {f : R → S → Work (ForInStep S)} (xs : List R) (s : S)
    (c : ℕ) (h : ∀ r t, Cheap (f r t) c) : Cheap (forIn xs s f) (xs.length*c) := by
  induction xs generalizing s with
  | nil => simpa only [List.forIn_nil,List.length_nil,Nat.zero_mul] using ret s
  | cons x xs ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm _ c]
    apply bind (h _ _); intro out; cases out with
    | done a => exact raise (ret a) (Nat.zero_le _)
    | yield a => exact ih a
def look (n : ℕ) := 2+(1+(4*n+1)+n*8)
def rootRate (n : ℕ) := 3+(2+(4*n+1)+n*look n)
def cost (n : ℕ) := 4*n+1+n*rootRate n+1

set_option maxRecDepth 3000 in
theorem two_color (n : ℕ) (a : Fin n → Fin n → Bool) : Cheap (twoColor n a) (cost n) := by
  unfold twoColor
  refine raise (tick (bind (v:=1) (list (List.finRange n) _ (rootRate n) ?_) ?_)) ?_
  · intro x st
    refine raise (tick (v:=2+((4*n+1)+n*look n)) ?_) ?_
    · split
      · refine raise (tick (tick (bind (v:=0) (list (List.range n) _ (look n) ?_) ?_))) (by simp)
        · intro z ac
          refine raise (tick (v:=1+((4*n+1)+n*8)) ?_) ?_
          · split
            · refine raise (tick (tick (bind (v:=0) (list (List.finRange n) _ 8 ?_) ?_))) (by simp)
              · intro w ac'
                refine raise (tick (v:=3) ?_) ?_
                · split
                  · split
                    · exact raise (tick (ret _)) (by decide)
                    · apply raise (tick (v:=0) ?_) (by decide)
                      split <;> exact ret _
                  · exact raise (ret _) (by decide)
                · decide
              · intro out; exact ret _
            · exact raise (ret _) (Nat.zero_le _)
          · simp [look,Nat.add_assoc]
        · intro out; exact ret _
      · exact raise (ret _) (Nat.zero_le _)
    · simp [rootRate,Nat.add_assoc]
  · intro out; exact tick (ret _)
  · simp [cost,Nat.add_assoc]
end ColorCost

end

section
open CapacitatedAssort.General BerkowitzModel BipHamCount.Deterministic
namespace ColorDFS
theorem cubic (n : ℕ) : ColorCost.cost n ≤ 100*(n+1)^3 := by
  unfold ColorCost.cost ColorCost.rootRate ColorCost.look
  ring_nf; omega
theorem certified {n} (g : Fin n → Fin n → Bool) (hg : IsBipartiteDigraph g) :
    Budget (twoColor n g) (fun o => ∃ f, o=some f ∧ ∀ u w, g u w=true → f u ≠ f w) (100*(n+1)^3) := by
  constructor; intro s
  exact ⟨(color_ok g hg).run s,(ColorCost.two_color n g s).trans (Nat.add_le_add_left (cubic n) s)⟩
end ColorDFS

end

section
open BipHamCount.Deterministic
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (adj : Fin n → Fin n → Bool),
      IsBipartiteDigraph adj →
        ((countHamCycles n adj).run 0).1 = hamCount adj ∧ 
        (((countHamCycles n adj).run 0).2 : ℝ) ≤ C * (19526/10000 : ℝ)^n :=
  BipHamFront.from_color_certificate ColorDFS.certified

end
