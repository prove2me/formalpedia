-- Prove2me | solution 1 for BipHamCount.Deterministic.berkowitz_bit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:31:50.958805+00:00
-- url     : https://prove2.me/submissions/6c9a5465-af90-41c0-9484-a53cee3eea8d

import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity
import Mathlib.Tactic

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

namespace BerkowitzModel
open BipHamCount.Deterministic CapacitatedAssort.General Polynomial Finset
open scoped Polynomial

noncomputable def polyEval (a : ZPoly) : ℤ[X] :=
  ∑ i ∈ range a.size, monomial i (a[i]?.getD 0)

theorem coeff_polyEval (a : ZPoly) (i : ℕ) : (polyEval a).coeff i = a[i]?.getD 0 := by
  simp only [polyEval,finsetSum_coeff,coeff_monomial]
  by_cases hi : i < a.size
  · rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hi)]
    · simp
    · intro j _ hj; simp [hj]
  · rw [Array.getElem?_eq_none (by omega : a.size ≤ i)]
    refine Finset.sum_eq_zero fun j hj => ?_
    have : j ≠ i := by have := Finset.mem_range.mp hj; omega
    simp [this]

private lemma coeff_fromPrefix (a : Array ℤ) (p : ℤ[X]) (d : ℕ)
    (hp : Prefix intOps id a d (fun i => p.coeff i)) (hn : ∀ i, d ≤ i → p.coeff i = 0) :
    polyEval a = p := by
  ext i
  rw [coeff_polyEval]
  by_cases hi : i < d
  · exact hp.atLt i hi
  · rw [hn i (by omega),Array.getElem?_eq_none (by have := hp.size; omega : a.size ≤ i)]; rfl

private theorem zaddPost (x y : ℤ) : Post (zadd x y) (· = x+y) := ⟨fun _ => rfl⟩
private theorem zsubPost (x y : ℤ) : Post (zsub x y) (· = x-y) := ⟨fun _ => rfl⟩
private theorem zmulPost (x y : ℤ) : Post (zmul x y) (· = x*y) := ⟨fun _ => rfl⟩

theorem integerRingModel : RingModel intOps id :=
  ⟨rfl,rfl,zaddPost,zmulPost,fun x => postMono (zsubPost 0 x) (by intro z hz; simpa using hz)⟩

theorem paddPost (a b : ZPoly) : Post (padd a b) (fun p => polyEval p = polyEval a + polyEval b) := by
  let d := max a.size b.size
  rw [padd]
  apply tickPost
  apply bindPost (Q := fun z => Prefix intOps id z d (fun i => (polyEval a + polyEval b).coeff i))
  · apply arrayLoop
    intro k hk xs hx
    apply tickPost
    apply bindPost (zaddPost _ _)
    intro x h
    apply purePost
    apply prefixPush hx
    simpa [coeff_polyEval] using h
  intro x hx
  apply purePost
  apply coeff_fromPrefix x _ d hx
  intro i hi
  have ha : a.size ≤ i := le_trans (le_max_left ..) hi
  have hb : b.size ≤ i := le_trans (le_max_right ..) hi
  simp [coeff_polyEval,Array.getElem?_eq_none ha, Array.getElem?_eq_none hb]

private lemma decode_bump (a : ZPoly) {i : ℕ} (hi : i < a.size) (v : ℤ) :
    polyEval (a.set! i ((a[i]?.getD 0)+v)) = polyEval a + monomial i v := by
  ext j
  simp only [coeff_polyEval,coeff_add,coeff_monomial,Array.set!_eq_setIfInBounds]
  by_cases h : i = j
  · subst j; rw [Array.getElem?_setIfInBounds_self_of_lt hi]; simp
  · rw [Array.getElem?_setIfInBounds_ne h]; simp [h]

private lemma decode_zeros (n : ℕ) : polyEval (Array.replicate n (0 : ℤ)) = 0 := by
  ext i
  by_cases h : i < n <;> simp [coeff_polyEval,Array.getElem?_replicate,h]

private noncomputable def factor (a : ZPoly) (i : ℕ) : ℤ[X] := monomial i (a[i]?.getD 0)

theorem pmulPost (a b : ZPoly) : Post (pmul a b) (fun c => polyEval c = polyEval a * polyEval b) := by
  rw [pmul]
  apply tickPost
  let N := a.size+b.size
  let invariant := fun k (z : ZPoly) =>
    z.size = N ∧ polyEval z = ∑ i ∈ range k, ∑ j ∈ range b.size, factor a i * factor b j
  apply bindPost (Q := invariant a.size)
  · apply rangePost invariant
    · simp [invariant,N,decode_zeros]
    · intro i hi z hz
      obtain ⟨hsize, hp⟩ := hz
      apply tickPost
      let invJ := fun k (u : ZPoly) => u.size = N ∧
        polyEval u = polyEval z + ∑ j ∈ range k, factor a i * factor b j
      apply bindPost (Q := invJ b.size)
      · apply rangePost invJ
        · simp [invJ,hsize]
        · intro j hj u hu
          obtain ⟨hus,hu⟩ := hu
          apply tickPost
          apply bindPost (zmulPost _ _)
          intro v hv
          apply bindPost (zaddPost _ _)
          intro w hw
          apply purePost
          change invJ (j+1) _
          constructor
          · simp [hus]
          · rw [hw, decode_bump _ (by dsimp [N] at hus; omega) _, hu,Finset.sum_range_succ,hv]
            simp [factor,monomial_mul_monomial,add_assoc]
      intro u hu
      apply purePost
      change invariant (i+1) u
      exact ⟨hu.1,by rw [hu.2,hp,Finset.sum_range_succ]⟩
  intro z hz
  apply purePost
  rw [hz.2]
  simp only [polyEval,factor,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm


private lemma negList (l : List ℤ) (a : Array ℤ) :
    Post (forIn l a fun x (b : Array ℤ) => do
      charge 2
      let c ← zsub 0 x
      return ForInStep.yield (b.push c))
      (fun out => out.toList = a.toList ++ l.map (-·)) := by
  induction l generalizing a with
  | nil => simp only [List.forIn_nil,List.map_nil,List.append_nil]; exact purePost rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (Q := (· = .yield (a.push (-x))))
    · apply tickPost
      apply bindPost (zsubPost _ _)
      intro c hc
      apply purePost
      simp [hc]
    intro y hy
    subst y
    apply postMono (ih _)
    intro out h
    simpa using h

theorem pnegPost (a : ZPoly) : Post (pneg a) (fun c => polyEval c = - polyEval a) := by
  rw [pneg]
  apply tickPost
  have hneg := negList a.toList #[]
  rw [Array.forIn_toList] at hneg
  apply bindPost hneg
  intro out hout
  apply purePost
  ext i
  simp only [coeff_neg,coeff_polyEval]
  have h := congrArg (fun l : List ℤ => l[i]?) hout
  simp only [Array.toList_empty,List.nil_append,Array.getElem?_toList,List.getElem?_map] at h
  rw [h]
  cases a[i]? <;> simp

theorem polyRingModel : RingModel polyOps polyEval := by
  refine ⟨?_,?_,paddPost,pmulPost,pnegPost⟩
  · simp [polyOps,polyEval]
  · simp [polyOps,polyEval,Finset.sum_range_succ]

end BerkowitzModel
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

namespace BerkowitzModel
open BipHamCount.Deterministic CapacitatedAssort.General Finset Polynomial
open scoped Polynomial

def polyFits (a : ZPoly) (u : ℕ) : Prop :=
  a.size ≤ u ∧ ∀ i : ℕ, (a[i]?.getD 0).natAbs ≤ 2^u

def opCost (g : ℕ) : ℕ := 100*(g+2)^4

lemma polyFits_mono {a : ZPoly} {u v : ℕ} (ha : polyFits a u) (hu : u ≤ v) : polyFits a v :=
  ⟨ha.1.trans hu,fun i => (ha.2 i).trans (Nat.pow_le_pow_right (by decide) hu)⟩

lemma intBits {x : ℤ} {b : ℕ} (h : x.natAbs ≤ 2^b) : x.natAbs.size ≤ b+1 :=
  Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos b; omega))

private lemma sum_bound (a b : ℤ) (u v : ℕ) (ha : a.natAbs ≤ 2^u) (hb : b.natAbs ≤ 2^v) :
    (a+b).natAbs ≤ 2^(max u v+1) := by
  apply (Int.natAbs_add_le a b).trans
  rw [pow_succ]
  have h₁ := ha.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left u v))
  have h₂ := hb.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right u v))
  omega

private lemma zbudget (f : ℤ → ℤ → Work ℤ) (g : ℤ → ℤ → ℤ) (hf : ∀ a b s,
    (f a b).run s = (g a b, s + (a.natAbs.size+b.natAbs.size+1)^2))
    (a b : ℤ) (u v : ℕ) (ha : a.natAbs.size ≤ u) (hb : b.natAbs.size ≤ v) :
    Budget (f a b) (· = g a b) ((u+v+1)^2) := by
  constructor; intro s; rw [hf]
  exact ⟨rfl,Nat.add_le_add_left (Nat.pow_le_pow_left (by omega) _) s⟩

private lemma zaddBudget (a b : ℤ) (u v : ℕ) (ha : a.natAbs.size ≤ u) (hb : b.natAbs.size ≤ v) :
    Budget (zadd a b) (· = a+b) ((u+v+1)^2) := zbudget _ _ (fun _ _ _ => rfl) _ _ _ _ ha hb

private lemma zmulBudget (a b : ℤ) (u v : ℕ) (ha : a.natAbs.size ≤ u) (hb : b.natAbs.size ≤ v) :
    Budget (zmul a b) (· = a*b) ((u+v+1)^2) := zbudget _ _ (fun _ _ _ => rfl) _ _ _ _ ha hb

theorem padd_budget {a b : ZPoly} {u v g : ℕ} (hu : u ≤ g) (hv : v ≤ g)
    (ha : polyFits a u) (hb : polyFits b v) :
    Budget (padd a b) (fun p => polyFits p (max u v+1)) (opCost g) := by
  let d := max a.size b.size
  have hd : d ≤ max u v := max_le_max ha.1 hb.1
  have hdg : d ≤ g := hd.trans (max_le hu hv)
  rw [padd]
  refine bLe (bTick (bBind (Q := fun x : ZPoly => x.size = d ∧ ∀ i < d, (x[i]?.getD 0).natAbs ≤ 2^(max u v+1))
    (w := 0) (u := d * (4+(g+1+(g+1)+1)^2+0)) ?_ ?_)) ?_
  · apply bRange (fun k (x : ZPoly) => x.size = k ∧ ∀ i < k, (x[i]?.getD 0).natAbs ≤ 2^(max u v+1))
    · simp
    · intro i hi z hz
      refine bLe (bTick (bBind (w := 0) (zaddBudget _ _ (g+1) (g+1)
        ((intBits (ha.2 i)).trans (by omega)) ((intBits (hb.2 i)).trans (by omega))) ?_)) (by omega)
      intro y hy
      apply bPure
      change (z.push y).size = _ ∧ _
      constructor
      · simp [hz.1]
      · intro j hj
        rw [Array.getElem?_push,hz.1]
        by_cases hji : j=i
        · rw [if_pos hji]; simpa [hy] using sum_bound (a[i]?.getD 0) (b[i]?.getD 0) u v (ha.2 i) (hb.2 i)
        · rw [if_neg hji]; exact hz.2 j (by omega)
  · intro z hz; apply bPure
    refine ⟨by omega,fun i => ?_⟩
    by_cases hi : i < d
    · exact hz.2 i hi
    · simp [Array.getElem?_eq_none (by omega : z.size ≤ i)]
  · calc
      _ ≤ (4*g+1)+(g * (4+(g+1+(g+1)+1)^2+0)+0) := by simp only [Nat.add_zero]; gcongr
      _ ≤ _ := by unfold opCost; ring_nf; omega


private theorem pnegListBudget (l : List ℤ) (b : ZPoly) (g : ℕ)
    (hl : ∀ x ∈ l, x.natAbs ≤ 2^g) :
    Budget (forIn l b fun x (out : Array ℤ) => do
      charge 2
      let c ← zsub 0 x
      return ForInStep.yield (out.push c))
      (fun out => out.size = b.size+l.length) (l.length*(2+(g+2)^2)) := by
  induction l generalizing b with
  | nil => rw [List.forIn_nil]; simpa using (bPure (rfl : b.size=b.size) : Budget (pure b) _ 0)
  | cons x xs ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*_) _]
    apply bBind (Q := fun z => z = .yield (b.push (-x)))
    · refine bLe (bTick (bBind (w := 0) (zbudget zsub (·-·) (fun _ _ _ => rfl)
        0 x 0 (g+1) (by decide) (intBits (hl x (by simp)))) ?_)) ?_
      · intro z hz; apply bPure; simp [hz]
      · simp
    · intro z hz; subst z
      apply bMap (ih _ (fun t ht => hl t (by simp [ht])))
      intro y hy; simp only [Array.size_push] at hy; omega

theorem pneg_budget {a : ZPoly} {u g : ℕ} (hu : u ≤ g) (ha : polyFits a u) :
    Budget (pneg a) (fun z => polyFits z u) (opCost g) := by
  have hs : ∀ x ∈ a.toList, x.natAbs ≤ 2^g := by
    intro x hx
    obtain ⟨i,hi,hix⟩ := List.getElem_of_mem hx
    have hai : i < a.size := by simpa using hi
    have h := (polyFits_mono ha hu).2 i
    simpa [Array.getElem?_eq_getElem hai,← hix] using h
  have hn := pnegListBudget a.toList #[] g hs
  rw [Array.forIn_toList] at hn
  have hl : Budget (pneg a) (fun z => z.size = a.size) (opCost g) := by
    rw [pneg]
    apply bLe (bTick (bBind (w := 0) hn (fun z hz => bPure (by simpa using hz))))
    have hag := ha.1.trans hu
    simp only [Array.length_toList,Nat.add_zero]
    calc _ ≤ 4*g+1+g*(2+(g+2)^2) := by gcongr
         _ ≤ _ := by unfold opCost; ring_nf; omega
  apply bMap (bValue hl (pnegPost a))
  intro z hz
  refine ⟨hz.1 ▸ ha.1,fun i => ?_⟩
  rw [← coeff_polyEval,hz.2,coeff_neg,Int.natAbs_neg,coeff_polyEval]
  exact ha.2 i

private lemma coeff_product_bound {a b : ZPoly} {u v : ℕ} (ha : polyFits a u) (hb : polyFits b v) (k : ℕ) :
    ((polyEval a * polyEval b).coeff k).natAbs ≤ 2^(2*u+v+2) := by
  conv => lhs; rw [polyEval,Finset.sum_mul,finsetSum_coeff]
  apply (Int.natAbs_sum_le _ _).trans
  apply (Finset.sum_le_sum (g := fun _ => 2^(u+v)) ?_).trans
  · simp only [sum_const,card_range,smul_eq_mul]
    calc _ ≤ 2^u * 2^(u+v) := Nat.mul_le_mul_right _ (ha.1.trans (Nat.lt_two_pow_self.le))
         _ ≤ _ := by rw [←pow_add]; apply Nat.pow_le_pow_right (by decide); omega
  · intro i _
    rw [← C_mul_X_pow_eq_monomial, mul_assoc,coeff_C_mul,coeff_X_pow_mul']
    split
    next h => rw [Int.natAbs_mul,coeff_polyEval,pow_add]; exact Nat.mul_le_mul (ha.2 i) (hb.2 _)
    next h => simp

private lemma bounded_store (out : ZPoly) (k : ℕ) (x : ℤ) (B : ℕ)
    (h : ∀ i : ℕ, (out[i]?.getD 0).natAbs ≤ B) (hx : x.natAbs ≤ B) :
    ∀ i : ℕ, ((out.set! k x)[i]?.getD 0).natAbs ≤ B := by
  intro i
  rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds]
  by_cases he : k=i
  · subst i; by_cases hk : k<out.size <;> simp [hk,hx]
  · simp [he,h]

theorem pmul_budget {a b : ZPoly} {u v g : ℕ} (hu : u ≤ g) (hv : v ≤ g)
    (ha : polyFits a u) (hb : polyFits b v) :
    Budget (pmul a b) (fun p => polyFits p (2*u+v+2)) (opCost g) := by
  let N := a.size+b.size
  let B := 2^(u+v)
  let t := 6+(g+1+(g+1)+1)^2+(4*g+1+(2*g+1)+1)^2
  let inv := fun k (x : ZPoly) => x.size=N ∧ ∀ i : ℕ, (x[i]?.getD 0).natAbs ≤ k*B
  have hag := ha.1.trans hu
  have hbg := hb.1.trans hv
  have hprod (x y : ℤ) (hx : x.natAbs ≤ 2^u) (hy : y.natAbs ≤ 2^v) : (x*y).natAbs ≤ B := by
    dsimp [B]; rw [pow_add,Int.natAbs_mul]; exact Nat.mul_le_mul hx hy
  have hbG : B ≤ 2^(2*g) := Nat.pow_le_pow_right (by decide) (by omega)
  have habG : a.size*b.size ≤ 2^(2*g) := by
    rw [two_mul,pow_add]; exact Nat.mul_le_mul (hag.trans Nat.lt_two_pow_self.le) (hbg.trans Nat.lt_two_pow_self.le)
  have hcap (k : ℕ) (hk : k ≤ a.size*b.size) : k*B ≤ 2^(4*g) := by
    rw [show 4*g = 2*g+2*g by omega,pow_add]
    exact Nat.mul_le_mul (hk.trans habG) hbG
  have raw : Budget (pmul a b) (inv (a.size*b.size)) (opCost g) := by
    rw [pmul]
    refine bLe (bTick (bBind (w := 0) (u := a.size*(4*b.size+1+b.size*t+0)) ?_ (fun x hx => bPure hx))) ?_
    · apply bRange (fun i => inv (i*b.size))
      · simp only [zero_mul]; constructor
        · simp [N]
        · intro j; by_cases hj : j < N <;> simp [N] at hj ⊢ <;> simp [hj]
      · intro i hi x hx
        refine bLe (bTick (bBind (w := 0) (u := b.size*t) (Q := inv (i*b.size+b.size)) ?_ ?_)) (by omega)
        · apply bRange (fun j => inv (i*b.size+j))
          · simpa using hx
          · intro j hj y hy
            have hxy : i*b.size+j ≤ a.size*b.size := calc
              _ ≤ (i+1)*b.size := by rw [Nat.add_mul]; omega
              _ ≤ _ := Nat.mul_le_mul_right _ hi
            have hpre := (hy.2 (i+j)).trans (hcap _ hxy)
            refine bLe (bTick (bBind (w := (4*g+1+(2*g+1)+1)^2+0)
              (zmulBudget _ _ (g+1) (g+1) ((intBits (ha.2 i)).trans (by omega)) ((intBits (hb.2 j)).trans (by omega))) ?_)) ?_
            · intro z hz
              have hzp := hprod _ _ (ha.2 i) (hb.2 j)
              refine bBind (w := 0) (zaddBudget _ _ (4*g+1) (2*g+1)
                (intBits hpre) (intBits (hz ▸ hzp.trans hbG))) ?_
              intro new hnew
              apply bPure
              change inv (i*b.size+(j+1)) (y.set! _ new)
              constructor
              · simp [hy.1]
              · have hnext : (i*b.size+(j+1))*B = (i*b.size+j)*B+B := by ring
                rw [hnext]
                apply bounded_store
                · intro e; exact (hy.2 e).trans (Nat.le_add_right ..)
                · rw [hnew,hz]; exact (Int.natAbs_add_le ..).trans (Nat.add_le_add (hy.2 _) hzp)
            · dsimp [t]; omega
        · intro z hz; apply bPure
          change inv ((i+1)*b.size) z
          simpa [Nat.add_mul] using hz
    · dsimp [t]
      calc
        _ ≤ 4*(g+g+1)+(g*(4*g+1+g*(6+(g+1+(g+1)+1)^2+(4*g+1+(2*g+1)+1)^2)+0)+0) := by simp only [Nat.add_zero]; gcongr
        _ ≤ _ := by unfold opCost; ring_nf; omega
  apply bMap (bValue raw (pmulPost a b))
  intro z hz
  refine ⟨by have := hz.1.1; dsimp [N] at this; have := ha.1; have := hb.1; omega,fun k => ?_⟩
  rw [← coeff_polyEval,hz.2]
  exact coeff_product_bound ha hb k

end BerkowitzModel
open CapacitatedAssort.General BipHamCount.Deterministic
namespace BerkowitzModel

structure CostModel {R : Type} (O : RingOps R) (Fits : R → ℕ → Prop) : Prop where
  mono {x u v} : Fits x u → u ≤ v → Fits x v
  zero : Fits O.zero 1
  one : Fits O.one 1
  neg {x u g} : u ≤ g → Fits x u → Budget (O.neg x) (fun y => Fits y u) (opCost g)
  add {x y u v g} : u ≤ g → v ≤ g → Fits x u → Fits y v →
    Budget (O.add x y) (fun z => Fits z (max u v+1)) (opCost g)
  mul {x y u v g} : u ≤ g → v ≤ g → Fits x u → Fits y v →
    Budget (O.mul x y) (fun z => Fits z (2*u+v+2)) (opCost g)

theorem polynomialCostModel : CostModel polyOps polyFits := by
  refine ⟨polyFits_mono,?_,?_,pneg_budget,padd_budget,pmul_budget⟩
  · constructor <;> simp [polyOps]
  · constructor
    · decide
    · intro i; cases i <;> simp [polyOps]

def intFits (x : ℤ) (u : ℕ) := x.natAbs ≤ 2^u

theorem integerCostModel : CostModel intOps intFits := by
  have cost (g : ℕ) : (g+1+(g+1)+1)^2 ≤ opCost g := by unfold opCost; ring_nf; omega
  refine ⟨?_,by change (0 : ℕ) ≤ 2; decide,by change (1 : ℕ) ≤ 2; decide,?_,?_,?_⟩
  · intro x u v h huv; exact h.trans (Nat.pow_le_pow_right (by decide) huv)
  · intro x u g h hx
    constructor; intro s
    refine ⟨by change (0-x).natAbs ≤ _; simpa [intFits] using hx,?_⟩
    change s+(0 + x.natAbs.size+1)^2 ≤ _
    apply Nat.add_le_add_left
    exact (Nat.pow_le_pow_left (by have := intBits hx; omega) _).trans (cost g)
  · intro x y u v g hu hv hx hy
    constructor; intro s
    refine ⟨?_,?_⟩
    · change (x+y).natAbs ≤ _
      apply (Int.natAbs_add_le ..).trans
      rw [pow_succ]
      have h1 := hx.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_left u v))
      have h2 := hy.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right u v))
      omega
    · change s+(x.natAbs.size+y.natAbs.size+1)^2 ≤ _
      apply Nat.add_le_add_left; exact (Nat.pow_le_pow_left (by have := intBits hx; have := intBits hy; omega) _).trans (cost g)
  · intro x y u v g hu hv hx hy
    constructor; intro s
    refine ⟨?_,?_⟩
    · change (x*y).natAbs ≤ _
      rw [Int.natAbs_mul]
      apply (Nat.mul_le_mul hx hy).trans
      rw [← pow_add]; apply Nat.pow_le_pow_right (by decide); omega
    · change s+(x.natAbs.size+y.natAbs.size+1)^2 ≤ _
      apply Nat.add_le_add_left; exact (Nat.pow_le_pow_left (by have := intBits hx; have := intBits hy; omega) _).trans (cost g)

variable {R : Type} {O : RingOps R} {Fits : R → ℕ → Prop}
def bufFits (O : RingOps R) (Fits : R → ℕ → Prop) (a : Array R) (u : ℕ) : Prop :=
  ∀ i : ℕ, Fits (a[i]?.getD O.zero) u
def matrixFits (O : RingOps R) (Fits : R → ℕ → Prop) (a : Array (Array R)) (u : ℕ) : Prop :=
  ∀ i : ℕ, bufFits O Fits (a[i]?.getD #[]) u

theorem bufEmpty (h : CostModel O Fits) {u : ℕ} (hu : 1 ≤ u) : bufFits O Fits #[] u := by
  intro i; simpa using h.mono h.zero hu
theorem bufPush {a : Array R} {u : ℕ} {x : R} (ha : bufFits O Fits a u) (hx : Fits x u) :
    bufFits O Fits (a.push x) u := by
  intro i; rw [Array.getElem?_push]; split
  next _ => exact hx
  next _ => exact ha i
theorem bufMono (h : CostModel O Fits) {a : Array R} {u v : ℕ} (ha : bufFits O Fits a u) (hu : u ≤ v) :
    bufFits O Fits a v := fun i => h.mono (ha i) hu

def vBound (d u l : ℕ) : ℕ := u+l*(2*u+d+4)
def tBound (d u : ℕ) : ℕ := vBound d u (d+1)
def cBound (d u n : ℕ) : ℕ := 1+n*(2*tBound d u+d+4)
def cap (d u : ℕ) : ℕ := cBound d u (d+1)+tBound d u+u+d+5
def basicTime (d u : ℕ) : ℕ := opCost (cap d u)+8*(d+3)+16
def layerTime1 (d u : ℕ) : ℕ := 16*(d+3)*basicTime d u
def layerTime2 (d u : ℕ) : ℕ := 16*(d+3)*layerTime1 d u
def layerTime3 (d u : ℕ) : ℕ := 16*(d+3)*layerTime2 d u
def coefficientTime (d u n : ℕ) : ℕ := (n+1)*(10*layerTime3 d u)

theorem mulAcc (h : CostModel O Fits) (x y acc : R) (u v j g : ℕ) (hu : u ≤ g) (hv : v ≤ g)
    (hcap : 2*u+v+2+j ≤ g) (hx : Fits x u) (hy : Fits y v) (ha : Fits acc (2*u+v+2+j)) :
    Budget (do
      let z ← O.mul x y
      let z ← O.add acc z
      return ForInStep.yield z)
      (Yield (fun z => Fits z (2*u+v+2+(j+1)))) (2*opCost g) := by
  refine bLe (bBind (w := opCost g+0) (h.mul hu hv hx hy) ?_) (by omega)
  intro z hz
  refine bBind (w := 0) (h.add hcap (by omega : 2*u+v+2 ≤ g) ha hz) ?_
  intro t ht
  apply bPure
  change Fits t _
  exact h.mono ht (by omega)

theorem dotCap (h : CostModel O Fits) (M : Array (Array R)) (row off n u v g : ℕ) (xs : Array R)
    (hm : matrixFits O Fits M u) (hx : bufFits O Fits xs v) (hc : 2*u+v+2+n ≤ g) :
    Budget (forIn (List.range n) O.zero fun j acc => do
      charge 3
      let r ← matRead O M row (off+1+j)
      let z ← O.mul r (xs[j]?.getD O.zero)
      let a ← O.add acc z
      return ForInStep.yield a)
      (fun z => Fits z (2*u+v+2+n)) (n*(5+2*opCost g)) := by
  apply bRange (fun k a => Fits a (2*u+v+2+k))
  · exact h.mono h.zero (by omega)
  · intro j hj a ha
    have hr : Budget (matRead O M row (off+1+j)) (fun x => Fits x u) 2 :=
      ⟨fun s => ⟨hm _ _,le_rfl⟩⟩
    refine bLe (bTick (bBind (w := 2*opCost g) hr ?_)) (by omega)
    intro r hr
    apply mulAcc h r _ a u v j g (by omega) (by omega) (by omega) hr (hx j) ha

theorem convCap (h : CostModel O Fits) (i n u v g : ℕ) (t p : Array R)
    (ht : bufFits O Fits t u) (hp : bufFits O Fits p v) (hc : 2*u+v+2+(min i n+1) ≤ g) :
    Budget (forIn (List.range (min i n+1)) O.zero fun j acc => do
      charge 4
      let z ← O.mul (t[i-j]?.getD O.zero) (p[j]?.getD O.zero)
      let a ← O.add acc z
      return ForInStep.yield a)
      (fun z => Fits z (2*u+v+2+(min i n+1))) ((min i n+1)*(4+2*opCost g)) := by
  apply bRange (fun k a => Fits a (2*u+v+2+k))
  · exact h.mono h.zero (by omega)
  · intro j hj a ha
    exact bTick (mulAcc h _ _ a u v j g (by omega) (by omega) (by omega) (ht _) (hp _) ha)

end BerkowitzModel

namespace BerkowitzModel
open CapacitatedAssort.General BipHamCount.Deterministic
variable {R : Type} {O : RingOps R} {Fits : R → ℕ → Prop}

private lemma v_le {d u l : ℕ} (h : l ≤ d+1) : vBound d u l ≤ tBound d u := by
  unfold vBound tBound vBound; gcongr

private lemma c_le {d u n : ℕ} (h : n ≤ d+1) : cBound d u n ≤ cap d u := by
  unfold cap; apply le_trans (b := cBound d u (d+1)) ?_ (by omega)
  unfold cBound; gcongr

private lemma dot_le {d u n l : ℕ} (h : n ≤ d) : 2*u+vBound d u l+2+n ≤ vBound d u (l+1) := by
  unfold vBound; rw [Nat.add_mul]; omega

private lemma conv_le {d u n i : ℕ} (h : n ≤ d) :
    2*tBound d u+cBound d u n+2+(min i n+1) ≤ cBound d u (n+1) := by
  unfold cBound; rw [Nat.add_mul]; omega

private lemma nested_le (d t : ℕ) : t ≤ 16*(d+3)*t := by
  calc t = 1*t := by simp
       _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

private lemma budget_le (d t k : ℕ) (hk : k ≤ d+2) :
    k*(8*t) ≤ 16*(d+3)*t := by
  calc _ ≤ (d+2)*(8*t) := Nat.mul_le_mul_right _ hk
       _ ≤ _ := by ring_nf; omega

private lemma readFits (M : Array (Array R)) (u i j : ℕ) (hm : matrixFits O Fits M u) :
    Budget (matRead O M i j) (fun x => Fits x u) 2 :=
  ⟨fun s => ⟨hm i j,le_rfl⟩⟩

private lemma zeroArr (h : CostModel O Fits) (u : ℕ) (hu : 1 ≤ u) :
    bufFits O Fits #[] u := bufEmpty h hu

private def initVec (O : RingOps R) (M : Array (Array R)) (off n : ℕ) : Work (Array R) :=
  forIn (List.range n) #[] fun j xs => do
    charge 2
    let x ← matRead O M (off+1+j) off
    return ForInStep.yield (xs.push x)

private theorem initCost (h : CostModel O Fits) (M : Array (Array R)) (off n d u : ℕ)
    (hn : n ≤ d) (hu : 1 ≤ u) (hm : matrixFits O Fits M u) :
    Budget (initVec O M off n) (fun x => bufFits O Fits x u) (layerTime1 d u) := by
  apply bLe (c := n*4)
  · apply bRange (fun _ x => bufFits O Fits x u) (bufEmpty h hu)
    intro i hi xs hx
    refine bTick (bBind (w := 0) (readFits M u _ _ hm) ?_)
    intro item hi
    apply bPure
    exact bufPush hx hi
  · apply le_trans (b := n*(8*basicTime d u)) ?_ (budget_le _ _ _ (by omega))
    gcongr; unfold basicTime; omega

private def nextVec (O : RingOps R) (M : Array (Array R)) (off n : ℕ) (vec : Array R) : Work (Array R) :=
  forIn (List.range n) #[] fun i xs => do
    charge (4*n+1)
    let sum ← forIn (List.range n) O.zero fun j acc => do
      charge 3
      let v ← matRead O M (off+1+i) (off+1+j)
      let z ← O.mul v (vec[j]?.getD O.zero)
      let a ← O.add acc z
      return ForInStep.yield a
    charge 1
    return ForInStep.yield (xs.push sum)

private theorem nextCost (h : CostModel O Fits) (M : Array (Array R)) (off n d u l : ℕ) (vec : Array R)
    (hn : n ≤ d) (hl : l < n) (hm : matrixFits O Fits M u) (hv : bufFits O Fits vec (vBound d u l)) :
    Budget (nextVec O M off n vec) (fun xs => bufFits O Fits xs (vBound d u (l+1))) (layerTime2 d u) := by
  let G := cap d u
  have hg : tBound d u ≤ G := by dsimp [G,cap]; omega
  have hgrade := dot_le (u := u) (l := l) hn
  have hcap := hgrade.trans ((v_le (by omega)).trans hg)
  have hT : 4*n+1 ≤ basicTime d u := by unfold basicTime; omega
  have ht0 : basicTime d u ≤ layerTime1 d u := nested_le _ _
  have hop : 5+2*opCost G ≤ 8*basicTime d u := by dsimp [basicTime,G]; omega
  have hd : n*(5+2*opCost G) ≤ layerTime1 d u :=
    (Nat.mul_le_mul_left n hop).trans (budget_le _ _ _ (by omega))
  refine bLe (bRange (I := fun _ xs => bufFits O Fits xs (vBound d u (l+1))) ?_ ?_) (budget_le d (layerTime1 d u) n (by omega))
  · apply bufEmpty h; unfold vBound; rw [Nat.add_mul]; omega
  · intro i hi xs hx
    refine bLe (bTick (bBind (w := 1+0) (dotCap h M (off+1+i) off n u (vBound d u l) G vec hm hv hcap) ?_)) ?_
    · intro z hz
      exact bTick (bPure (bufPush hx (h.mono hz hgrade)))
    · omega

private def colUpdate (O : RingOps R) (M : Array (Array R)) (off n l : ℕ) (tv : Array R × Array R) :
    Work (ForInStep (Array R × Array R)) := do
  charge (4*n+1)
  let s ← forIn (List.range n) O.zero fun j acc => do
    charge 3
    let r ← matRead O M off (off+1+j)
    let z ← O.mul r (tv.2[j]?.getD O.zero)
    let a ← O.add acc z
    return ForInStep.yield a
  let ns ← O.neg s
  charge 1
  let t := tv.1.push ns
  if l+1 < n then
    charge (4*n+1)
    let v ← nextVec O M off n tv.2
    return ForInStep.yield (t,v)
  else return ForInStep.yield (t,tv.2)

private def stateOK (O : RingOps R) (Fits : R → ℕ → Prop) (n d u l : ℕ) (tv : Array R × Array R) :=
  bufFits O Fits tv.1 (tBound d u) ∧ (l < n → bufFits O Fits tv.2 (vBound d u l))

private lemma colCost (h : CostModel O Fits) (M : Array (Array R)) (off n d u l : ℕ) (tv : Array R × Array R)
    (hn : n ≤ d) (hl : l < n) (hm : matrixFits O Fits M u) (htv : stateOK O Fits n d u l tv) :
    Budget (colUpdate O M off n l tv) (Yield (stateOK O Fits n d u (l+1))) (8*layerTime2 d u) := by
  let G := cap d u
  let v := vBound d u l
  let q := 2*u+v+2+n
  have hT : q ≤ tBound d u := (dot_le hn).trans (v_le (by omega))
  have hG : tBound d u ≤ G := by dsimp [G,cap]; omega
  have hd := dotCap h M off off n u v G tv.2 hm (htv.2 hl) (hT.trans hG)
  have h0 : 4*n+1 ≤ basicTime d u := by unfold basicTime; omega
  have h1 : basicTime d u ≤ layerTime1 d u := nested_le _ _
  have h2 : layerTime1 d u ≤ layerTime2 d u := nested_le _ _
  have hc : opCost G ≤ basicTime d u := by dsimp [basicTime,G]; omega
  have hdT : n*(5+2*opCost G) ≤ layerTime1 d u :=
    (Nat.mul_le_mul_left n (show 5+2*opCost G ≤ 8*basicTime d u by dsimp [basicTime,G]; omega)).trans (budget_le _ _ _ (by omega))
  unfold colUpdate
  refine bLe (bTick (bBind (w := 4*layerTime2 d u) hd ?_)) (by omega)
  intro s hs
  refine bLe (bBind (w := 3*layerTime2 d u) (h.neg (hT.trans hG) hs) ?_) (by omega)
  intro ns hns
  refine bLe (bTick (c := 2*layerTime2 d u) ?_) (by omega)
  have hpush := bufPush htv.1 (h.mono hns hT)
  split
  next test =>
    refine bLe (bTick (bBind (w := 0) (nextCost h M off n d u l tv.2 hn hl hm (htv.2 hl)) ?_)) (by omega)
    intro nv hnv
    exact bPure ⟨hpush,fun _ => hnv⟩
  next test => exact bLe (bPure ⟨hpush,fun hh => (test hh).elim⟩) (by omega)


private def finishVec (O : RingOps R) (n : ℕ) (t p : Array R) : Work (Array R) :=
  forIn (List.range (n+2)) #[] fun i out => do
    charge (4*(min i n+1)+1)
    let s ← forIn (List.range (min i n+1)) O.zero fun j acc => do
      charge 4
      let z ← O.mul (t[i-j]?.getD O.zero) (p[j]?.getD O.zero)
      let a ← O.add acc z
      return ForInStep.yield a
    charge 1
    return ForInStep.yield (out.push s)

private lemma finishCost (h : CostModel O Fits) (d u n : ℕ) (hn : n+1 ≤ d) (t p : Array R)
    (ht : bufFits O Fits t (tBound d u)) (hp : bufFits O Fits p (cBound d u n)) :
    Budget (finishVec O n t p) (fun out => bufFits O Fits out (cBound d u (n+1))) (layerTime2 d u) := by
  let G := cap d u
  have h0 : 4*(n+1)+1 ≤ basicTime d u := by unfold basicTime; omega
  have h1 : basicTime d u ≤ layerTime1 d u := nested_le _ _
  have hop : 4+2*opCost G ≤ 8*basicTime d u := by dsimp [G,basicTime]; omega
  refine bLe (bRange (I := fun _ xs => bufFits O Fits xs (cBound d u (n+1))) ?_ ?_) (budget_le d _ (n+2) (by omega))
  · apply bufEmpty h; dsimp [cBound]; omega
  · intro i hi x hx
    have hg := conv_le (i := i) (u := u) (show n ≤ d by omega)
    have hc := convCap h i n (tBound d u) (cBound d u n) G t p ht hp (hg.trans (c_le (by omega)))
    have hT : (min i n+1)*(4+2*opCost G) ≤ layerTime1 d u :=
      (Nat.mul_le_mul_left _ hop).trans (budget_le _ _ _ (by omega))
    refine bLe (bTick (bBind (w := 1+0) hc ?_)) (by omega)
    intro z hz
    apply bTick; apply bPure
    exact bufPush hx (h.mono hz hg)

theorem coefficients_budget (h : CostModel O Fits) (M : Array (Array R)) (d u : ℕ) (hu : 1 ≤ u)
    (hm : matrixFits O Fits M u) (n off : ℕ) (hn : n ≤ d) :
    Budget (berkCoeffs O M n off) (fun p => bufFits O Fits p (cBound d u n)) (coefficientTime d u n) := by
  let G := cap d u
  have h0 : 4*(d+3)+1 ≤ basicTime d u := by unfold basicTime; omega
  have h1 : basicTime d u ≤ layerTime1 d u := nested_le _ _
  have h2 : layerTime1 d u ≤ layerTime2 d u := nested_le _ _
  have h3 : layerTime2 d u ≤ layerTime3 d u := nested_le _ _
  have hOp : opCost G ≤ basicTime d u := by dsimp [G,basicTime]; omega
  have huT : u ≤ tBound d u := by unfold tBound vBound; omega
  have huG : u ≤ G := by dsimp [G,cap]; omega
  induction n generalizing off with
  | zero =>
    rw [berkCoeffs.eq_1]
    have hbuf : bufFits O Fits #[O.one] (cBound d u 0) := by
      intro i
      simp only [cBound,Nat.zero_mul,Nat.add_zero]
      cases i with
      | zero => exact h.one
      | succ i =>
        rw [Array.getElem?_eq_none (by simp)]
        exact h.zero
    exact bLe (bTick (bPure hbuf)) (by change 1+0 ≤ 1*(10*layerTime3 d u); omega)
  | succ n ih =>
    rw [berkCoeffs.eq_2]
    have hn' : n ≤ d := by omega
    have hrec := ih (off+1) hn'
    have hnext : coefficientTime d u (n+1) = coefficientTime d u n+10*layerTime3 d u := by unfold coefficientTime; ring
    rw [hnext]
    refine bLe (bTick (bBind (w := 9*layerTime3 d u) hrec ?_)) (by omega)
    intro p hp
    refine bLe (bBind (w := 8*layerTime3 d u) (readFits M u off off hm) ?_) (by omega)
    intro a ha
    refine bLe (bBind (w := 7*layerTime3 d u) (h.neg huG ha) ?_) (by omega)
    intro na hna
    refine bLe (bTick (bBind (w := 5*layerTime3 d u) (initCost h M off n d u hn' hu hm) ?_)) (by omega)
    intro vec hvec
    have hin : stateOK O Fits n d u 0 (#[O.one,na],vec) := by
      refine ⟨?_,fun _ => ?_⟩
      · exact bufPush (bufPush (bufEmpty h (hu.trans huT)) (h.mono h.one (hu.trans huT))) (h.mono hna huT)
      · simpa [vBound] using hvec
    have ht := bRange (p := colUpdate O M off n) (stateOK O Fits n d u) hin
      (fun l hl tv htv => colCost h M off n d u l tv hn' hl hm htv)
    have htime : n*(8*layerTime2 d u) ≤ layerTime3 d u := budget_le d (layerTime2 d u) n (by omega)
    refine bLe (bTick (bBind (w := 3*layerTime3 d u) ht ?_)) (by change _ ≤ _; omega)
    intro tv htv
    refine bLe (bTick (bBind (w := 0) (finishCost h d u n hn tv.1 p htv.1 hp) ?_)) (by omega)
    intro out hout
    exact bPure hout

def determinantTime (n u : ℕ) := coefficientTime n u n+basicTime n u+basicTime n u

theorem determinant_budget (h : CostModel O Fits) (M : Array (Array R)) (n u : ℕ) (hu : 1 ≤ u)
    (hm : matrixFits O Fits M u) :
    Budget (berkowitz O n M) (fun x => Fits x (cBound n u n)) (determinantTime n u) := by
  rw [berkowitz]
  unfold determinantTime
  have hn : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have ht : n.size+3 ≤ basicTime n u := by unfold basicTime; omega
  have hop : opCost (cap n u) ≤ basicTime n u := by unfold basicTime; omega
  refine bLe (bBind (w := basicTime n u+basicTime n u) (coefficients_budget h M n u hu hm n 0 le_rfl) ?_) (by omega)
  intro p hp
  refine bLe (bTick (c := basicTime n u) ?_) (by omega)
  split
  next he => exact bLe (bPure (hp n)) (by omega)
  next he => exact bLe (h.neg (c_le (by omega : n ≤ n+1)) (hp n)) hop

end BerkowitzModel
open BipHamCount.Deterministic BerkowitzModel
theorem solution (n u : ℕ) (hu : 1 ≤ u) :
    let t := u + (n+1)*(2*u+n+4)
    let p := fun l : ℕ => 1+l*(2*t+n+4)
    let g := p (n+1)+t+u+n+5
    let b := 100*(g+2)^4+8*(n+3)+16
    let h := 16*(n+3)
    let w := (n+1)*(10*(h*(h*(h*b))))+b+b
    (∀ (M : Array (Array ℤ)) (s : ℕ),
      (∀ i j : ℕ, (((M[i]?.getD #[])[j]?).getD 0).natAbs ≤ 2^u) →
      let z := (berkowitz intOps n M).run s
      z.1.natAbs ≤ 2^(p n) ∧ z.2 ≤ s+w) ∧
    (∀ (M : Array (Array ZPoly)) (s : ℕ),
      (∀ i j : ℕ, let a := ((M[i]?.getD #[])[j]?).getD #[]
        a.size ≤ u ∧ ∀ k : ℕ, (a[k]?.getD 0).natAbs ≤ 2^u) →
      let z := (berkowitz polyOps n M).run s
      (z.1.size ≤ p n ∧ ∀ k : ℕ, (z.1[k]?.getD 0).natAbs ≤ 2^(p n)) ∧ z.2 ≤ s+w) := by
  constructor
  · intro M s hm
    exact (determinant_budget integerCostModel M n u hu hm).run s
  · intro M s hm
    exact (determinant_budget polynomialCostModel M n u hu hm).run s
