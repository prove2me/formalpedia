-- Prove2me | solution 1 for BipHamCount.Deterministic.largeSummand_spec
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:41:29.691845+00:00
-- url     : https://prove2.me/submissions/e3585286-6602-4125-adfc-3ebbad660745

import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds
import Definitions.Def_BipHamCount_Deterministic_Programs
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_det_correct
import Mathlib.Data.Finset.Sort
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

open BipHamCount.Deterministic BerkowitzModel CapacitatedAssort.General Finset
open scoped BigOperators

namespace LargeSumm
private lemma budgetListMap {α β : Type} (L : List α) (b : Array β)
    (f : α → β) (p : α → Array β → Work (ForInStep (Array β))) (c : ℕ)
    (hs : ∀ x a, Budget (p x a) (· = .yield (a.push (f x))) c) :
    Budget (forIn L b p) (fun y => y.toList = b.toList ++ L.map f) (L.length*c) := by
  induction L generalizing b with
  | nil => simp only [List.forIn_nil,List.length_nil,Nat.zero_mul,List.map_nil,List.append_nil]; apply bPure; rfl
  | cons x xs ih =>
    rw [List.forIn_cons,List.length_cons,Nat.succ_mul,Nat.add_comm (xs.length*c) _]
    apply bBind (hs x b)
    intro o ho; subst o
    apply bMap (ih _)
    intro y hy; simpa using hy

def buffer {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m)) : Array (Array ℤ) :=
  ((S.sort (· ≤ ·)).map (fun i => ((T.sort (· ≤ ·)).map (fun j => A i j)).toArray)).toArray

def minorTime (m : ℕ) := 8*(m+1)^3+m*(2+m*3+1)

theorem buffer_budget {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m)) :
    Budget (minorBuffer A S T) (· = buffer A S T) (minorTime m) := by
  let rows := S.sort (· ≤ ·); let cols := T.sort (· ≤ ·)
  rw [minorBuffer]
  have hc (i : Fin m) : Budget (forIn cols (#[] : Array ℤ) fun j row => do
      charge 3; return ForInStep.yield (row.push (A i j)))
      (fun z => z.toList = #[].toList ++ cols.map (A i)) (cols.length*3) :=
    budgetListMap cols #[] (A i) _ 3 (fun _ _ => ⟨fun _ => ⟨rfl,le_rfl⟩⟩)
  refine bLe (bTick (bBind (w := 0) (u := rows.length*(2+cols.length*3+1)) (Q := fun z =>
    z.toList = #[].toList ++ rows.map (fun i => (cols.map (A i)).toArray)) ?_ ?_)) ?_
  · apply budgetListMap
    intro i b
    refine bLe (bTick (bBind (w := 1+0) (hc i) ?_)) (by omega)
    intro r hr
    have he : r = (cols.map (A i)).toArray := by apply Array.toList_inj.mp; simpa using hr
    subst r
    exact ⟨fun _ => ⟨rfl,le_rfl⟩⟩
  · intro z hz
    apply bPure
    apply Array.toList_inj.mp
    simpa [buffer,rows,cols] using hz
  · unfold minorTime
    have hs : S.card ≤ m := by simpa using card_le_univ S
    have ht : T.card ≤ m := by simpa using card_le_univ T
    simp [rows,cols]; gcongr

theorem buffer_entries {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (S T : Finset (Fin m)) :
    matrixFits intOps intFits (buffer A S T) 1 := by
  intro i j
  change ((((buffer A S T)[i]?.getD #[])[j]?).getD 0).natAbs ≤ 2^1
  simp only [buffer,List.getElem?_toArray,List.getElem?_map]
  cases hi : (S.sort (· ≤ ·))[i]? with
  | none => simp
  | some x =>
    simp only [Option.map_some,Option.getD_some,List.getElem?_toArray,List.getElem?_map]
    cases hj : (T.sort (· ≤ ·))[j]? with
    | none => simp
    | some y => rcases hA x y with h|h <;> simp [h]

theorem buffer_det {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (S T : Finset (Fin m)) (h : T.card=S.card) (s : ℕ) :
    ((berkowitz intOps S.card (buffer A S T)).run s).1 = minor A S T := by
  rw [berkowitz_det_correct.1,minor,dif_pos h]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [buffer,List.getElem?_toArray,List.getElem?_map, squareSub,Matrix.submatrix_apply]
  have hi : i.val < (S.sort (· ≤ ·)).length := by simpa using i.isLt
  have hj : j.val < (T.sort (· ≤ ·)).length := by simpa [h] using j.isLt
  rw [List.getElem?_eq_getElem hi]
  simp only [Option.map_some,Option.getD_some,List.getElem?_toArray,List.getElem?_map]
  rw [List.getElem?_eq_getElem hj]
  rfl

private lemma grade_increasing {n m : ℕ} (hn : n ≤ m) : cBound n 1 n ≤ cBound m 1 m := by
  unfold cBound tBound vBound
  gcongr

private lemma time_increasing {n m : ℕ} (hn : n ≤ m) : determinantTime n 1 ≤ determinantTime m 1 := by
  unfold determinantTime coefficientTime layerTime3 layerTime2 layerTime1 basicTime opCost cap cBound tBound vBound
  gcongr

def outSize (m b : ℕ) : ℕ := 2*b+2*cBound m 1 m+1
def cost (m b : ℕ) : ℕ :=
  4*(m+1)+2*minorTime m+2*determinantTime m 1+(m+2)^2+4*(2*outSize m b+3)^2

private lemma signed (e s : ℕ) : ((paritySign e).run s).1 = (-1 : ℤ)^e := by
  change (if e%2=0 then 1 else -1) = _
  split
  next h => rw [(Nat.even_iff.mpr h).neg_one_pow]
  next h => rw [(Nat.not_even_iff_odd.mp (fun hh => h (Nat.even_iff.mp hh))).neg_one_pow]

private lemma mul_budget (x y : ℤ) (a b g : ℕ) (ha : x.natAbs ≤ 2^a) (hb : y.natAbs ≤ 2^b)
    (h₁ : a≤g) (h₂ : b≤g) :
    Budget (zmul x y) (fun z => z=x*y ∧ z.natAbs ≤ 2^(a+b)) ((2*g+3)^2) := by
  constructor; intro s
  refine ⟨⟨rfl,?_⟩,?_⟩
  · change (x*y).natAbs ≤ _
    rw [Int.natAbs_mul,pow_add]; exact Nat.mul_le_mul ha hb
  · change s+(x.natAbs.size+y.natAbs.size+1)^2 ≤ _
    have hsize (q r : ℕ) (h : q ≤ 2^r) : q.size ≤ r+1 :=
      Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos r; omega))
    exact Nat.add_le_add_left (Nat.pow_le_pow_left (by have := hsize _ _ ha; have := hsize _ _ hb; omega) _) _


theorem large_summand_budget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (S T : Finset (Fin m)) (hc : T.card = S.card) (pa pb : ℤ) (b : ℕ)
    (ha : pa.natAbs ≤ 2^b) (hb : pb.natAbs ≤ 2^b) :
    Budget (largeSummand A B S T pa pb) (fun out =>
      out = (-1 : ℤ)^(Sᶜ.card+1)*pa*pb*minor A Sᶜ Tᶜ*minor B Tᶜ Sᶜ ∧
      out.natAbs ≤ 2^(outSize m b)) (cost m b) := by
  let d := cBound m 1 m
  let g := outSize m b
  let t := (2*g+3)^2
  let dt := determinantTime m 1
  let bt := minorTime m
  have hSC : Sᶜ.card ≤ m := by simpa using card_le_univ Sᶜ
  have hc' : Tᶜ.card=Sᶜ.card := by simp [card_compl,hc]
  have hdet (H : Matrix (Fin m) (Fin m) ℤ) (hH : ZeroOne H) (I J : Finset (Fin m)) (hc : J.card=I.card) :
      Budget (berkowitz intOps I.card (buffer H I J))
        (fun z => z = minor H I J ∧ z.natAbs ≤ 2^d) dt := by
    have hcI : I.card ≤ m := by simpa using card_le_univ I
    have hh := uploaded_integer_determinant_budget (buffer H I J) I.card 1 le_rfl (buffer_entries H hH I J)
    constructor; intro s
    obtain ⟨hv,ht⟩ := hh.run s
    exact ⟨⟨buffer_det H I J hc s, hv.trans (Nat.pow_le_pow_right (by decide) (grade_increasing hcI))⟩,
      ht.trans (Nat.add_le_add_left (time_increasing hcI) _)⟩
  have hsign : Budget (paritySign (Sᶜ.card+1)) (fun z => z=(-1 : ℤ)^(Sᶜ.card+1) ∧ z.natAbs ≤ 2^1) ((m+2)^2) := by
    constructor; intro s
    have hr := signed (Sᶜ.card+1) s
    refine ⟨⟨hr,by rw [hr]; simp⟩,?_⟩
    change s+((Sᶜ.card+1).size+1)^2 ≤ _
    have hh : (Sᶜ.card+1).size ≤ Sᶜ.card+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    exact Nat.add_le_add_left (Nat.pow_le_pow_left (by omega) _) _
  have hg : g=2*b+2*d+1 := rfl
  unfold largeSummand
  refine bLe (bTick (bBind (w := bt+2*dt+(m+2)^2+4*t) (buffer_budget A Sᶜ Tᶜ) ?_)) ?_
  · intro ab hab; subst ab
    refine bLe (bBind (w := 2*dt+(m+2)^2+4*t) (buffer_budget B Tᶜ Sᶜ) ?_) (by dsimp [bt]; omega)
    intro bb hbb; subst bb
    refine bLe (bBind (w := dt+(m+2)^2+4*t) (hdet A hA Sᶜ Tᶜ hc') ?_) (by omega)
    intro da hda
    refine bLe (bBind (w := (m+2)^2+4*t) (hdet B hB Tᶜ Sᶜ hc'.symm) ?_) (by omega)
    intro db hdb
    refine bLe (bBind (w := 4*t) hsign ?_) (by omega)
    intro s hs
    refine bLe (bBind (w := 3*t) (mul_budget s pa 1 b g hs.2 ha (by omega) (by omega)) ?_) (by dsimp [t]; omega)
    intro x hx
    refine bLe (bBind (w := 2*t) (mul_budget x pb (1+b) b g hx.2 hb (by omega) (by omega)) ?_) (by dsimp [t]; omega)
    intro y hy
    refine bLe (bBind (w := t) (mul_budget y da (1+b+b) d g hy.2 hda.2 (by omega) (by omega)) ?_) (by dsimp [t]; omega)
    intro z hz
    apply bMap (mul_budget z db (1+b+b+d) d g hz.2 hdb.2 (by omega) (by omega))
    intro r hr
    refine ⟨by rw [hr.1,hz.1,hy.1,hx.1,hs.1,hda.1,hdb.1],?_⟩
    exact hr.2.trans (Nat.pow_le_pow_right (by decide) (by change _ ≤ g; omega))
  · unfold cost; dsimp [t,dt,bt,g]; omega

end LargeSumm
open BipHamCount.Deterministic
theorem solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (S T : Finset (Fin m)) (h : T.card = S.card)
    (a b : ℤ) (u : ℕ) (ha : a.natAbs ≤ 2^u) (hb : b.natAbs ≤ 2^u) (s : ℕ) :
    let t := 1+(m+1)*(2+m+4)
    let p := fun l : ℕ => 1+l*(2*t+m+4)
    let g := p (m+1)+t+1+m+5
    let β := 100*(g+2)^4+8*(m+3)+16
    let h := 16*(m+3)
    let w := (m+1)*(10*(h*(h*(h*β))))+β+β
    let v := 2*u+2*p m+1
    let ℓ := 8*(m+1)^3+m*(2+m*3+1)
    let z := (largeSummand A B S T a b).run s
    (z.1 = (-1 : ℤ)^(Sᶜ.card+1)*a*b*minor A Sᶜ Tᶜ*minor B Tᶜ Sᶜ ∧ z.1.natAbs ≤ 2^v) ∧
      z.2 ≤ s+(4*(m+1)+2*ℓ+2*w+(m+2)^2+4*(2*v+3)^2) := (LargeSumm.large_summand_budget A B hA hB S T h a b u ha hb).run s
