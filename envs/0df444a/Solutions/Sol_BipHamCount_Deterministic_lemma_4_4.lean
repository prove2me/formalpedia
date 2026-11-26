-- Prove2me | solution 1 for BipHamCount.Deterministic.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:42:05.326083+00:00
-- url     : https://prove2.me/submissions/453430fe-c3ac-4112-a0fc-69d84149c058

import Definitions.Def_BipHamCount_Deterministic_Programs
import Theorems.Thm_BipHamCount_Deterministic_computeF_correct
import Theorems.Thm_BipHamCount_Deterministic_berkowitz_bit_bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace BerkowitzModel
def Yield {α : Type} (Q : α → Prop) : ForInStep α → Prop
  | .yield x => Q x
  | .done _ => False
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

theorem bufPush {R : Type} {O : RingOps R} {Fits : R → ℕ → Prop}
    {a : Array R} {u : ℕ} {x : R} (ha : bufFits O Fits a u) (hx : Fits x u) :
    bufFits O Fits (a.push x) u := by
  intro i; rw [Array.getElem?_push]; split
  next _ => exact hx
  next _ => exact ha i
lemma intBits {x : ℤ} {b : ℕ} (h : x.natAbs ≤ 2^b) : x.natAbs.size ≤ b+1 :=
  Nat.size_le.mpr (h.trans_lt (by rw [pow_succ]; have := Nat.two_pow_pos b; omega))
end BerkowitzModel


open Finset CapacitatedAssort.General
open BipHamCount.Deterministic

private def sumBits {α : Type} (f : α → ℤ) (L : List α) (a : ℤ) : Work ℤ :=
  forIn L a fun i s => do
    charge 2
    let z ← zadd s (f i)
    return ForInStep.yield z

private theorem sumBits_spec {α : Type} (f : α → ℤ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (m : ℕ) (L : List α) (a : ℤ) (s : ℕ) (ha : a.natAbs + L.length ≤ m) :
    let r := (sumBits f L a).run s
    r.1 = a + (L.map f).sum ∧ r.1.natAbs ≤ a.natAbs + L.length ∧
      r.2 ≤ s + L.length * (2 + (m+2)^2) := by
  induction L generalizing a s with
  | nil =>
    change a = a + 0 ∧ a.natAbs ≤ a.natAbs + 0 ∧ s ≤ s + 0 * (2+(m+2)^2)
    simp
  | cons x xs ih =>
    have hx : (f x).natAbs ≤ 1 := by rcases hf x with h|h <;> simp [h]
    have hx' : (a + f x).natAbs ≤ a.natAbs + 1 := (Int.natAbs_add_le ..).trans (by omega)
    have ha' : (a+f x).natAbs + xs.length ≤ m := by simpa using show _ ≤ m from by simp at ha; omega
    let cost := (Nat.size a.natAbs + Nat.size (f x).natAbs + 1)^2
    have hs (n : ℕ) : n.size ≤ n := Nat.size_le.mpr (Nat.lt_two_pow_self)
    have hc : cost ≤ (m+2)^2 := by
      apply Nat.pow_le_pow_left; have := hs a.natAbs; have := hs (f x).natAbs; omega
    have ⟨h1,h2,h3⟩ := ih (a+f x) (s+2+cost) ha'
    simp only [sumBits, List.forIn_cons]
    change ((sumBits f xs (a+f x)).run (s+2+cost)).1 = _ ∧ ((sumBits f xs (a+f x)).run (s+2+cost)).1.natAbs ≤ _ ∧ ((sumBits f xs (a+f x)).run (s+2+cost)).2 ≤ _
    refine ⟨by rw [h1]; simp [add_assoc],by simp at *; omega,?_⟩
    simp only [List.length_cons, Nat.add_mul, one_mul]
    omega

theorem BipHamCount.Deterministic.computeW_bits {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ)
    (hA : ZeroOne A) (hB : ZeroOne B) (X Y : Finset (Fin m)) (i : Fin m) (s : ℕ) :
    ((computeW A B X Y i).run s).1 = w A B X Y i ∧
      ((computeW A B X Y i).run s).2 ≤ s + 100*(m+1)^3 := by
  let l := X.sort (· ≤ ·)
  let r := Y.sort (· ≤ ·)
  let st := s + 16*(m+1)^3
  let a := (sumBits (A i) l 0).run st
  let b := (sumBits (B · i) r 0).run a.2
  have hl : l.length ≤ m := by simpa [l] using card_le_univ X
  have hr : r.length ≤ m := by simpa [r] using card_le_univ Y
  have ⟨ha,ha1,ha2⟩ := sumBits_spec (A i) (hA i) m l 0 st (by simpa using hl)
  have ⟨hb,hb1,hb2⟩ := sumBits_spec (B · i) (fun j => hB j i) m r 0 a.2 (by simpa using hr)
  change a.1*b.1 = _ ∧ b.2 + (a.1.natAbs.size+b.1.natAbs.size+1)^2 ≤ _
  constructor
  · rw [show a.1 = _ from ha,show b.1 = _ from hb]
    simp only [zero_add,w]
    congr 1
    · exact ((X.sort_perm_toList (· ≤ ·)).map _).sum_eq.trans (X.sum_map_toList _)
    · exact ((Y.sort_perm_toList (· ≤ ·)).map _).sum_eq.trans (Y.sum_map_toList _)
  · have hsizea : a.1.natAbs.size ≤ m := by
      exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (by simpa using ha1.trans (by simpa using hl))
    have hsizeb : b.1.natAbs.size ≤ m := by
      exact (Nat.size_le.mpr (Nat.lt_two_pow_self)).trans (by simpa using hb1.trans (by simpa using hr))
    have hc : (a.1.natAbs.size+b.1.natAbs.size+1)^2 ≤ (m+m+1)^2 := Nat.pow_le_pow_left (by omega) _
    change b.2 + _ ≤ _
    change a.2 ≤ st + _ at ha2
    change b.2 ≤ a.2 + _ at hb2
    dsimp [st] at ha2
    have h1 := Nat.mul_le_mul_right (2+(m+2)^2) hl
    have h2 := Nat.mul_le_mul_right (2+(m+2)^2) hr
    nlinarith

open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel Finset
open scoped BigOperators
namespace EvaluationBudget
private lemma abs_sum_bound {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ)
    (h : ∀ i ∈ s, (f i).natAbs ≤ b) : (∑ i ∈ s, f i).natAbs ≤ s.card * b := by
  apply (Int.natAbs_sum_le s f).trans
  simpa using Finset.sum_le_sum h

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


def width (m : ℕ) := (m+2)^2
def dotTime (m : ℕ) := (m+1)*(13+(m+2)^2)

private def dotGo {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (i j : Fin m)
    (zs : List (Fin m)) (c : ℤ) : Work ℤ :=
  forIn zs c fun z a => do
    charge 3
    let p ← zmul (A i z) (B z j)
    let x ← zadd a p
    return .yield x

private theorem dotGo_bound {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (hB : ZeroOne B) (i j : Fin m) (zs : List (Fin m)) (a : ℤ) (s : ℕ)
    (ha : a.natAbs+zs.length ≤ m) :
    ((dotGo A B i j zs a).run s).1.natAbs ≤ m ∧
    ((dotGo A B i j zs a).run s).2 ≤ s+zs.length*(13+(m+2)^2) := by
  induction zs generalizing a s with
  | nil => change a.natAbs ≤ m ∧ s ≤ s+0*_; simpa using ha
  | cons z zs ih =>
    let p := A i z*B z j
    have ap : (A i z).natAbs ≤ 1 := by rcases hA i z with h|h <;> simp [h]
    have bp : (B z j).natAbs ≤ 1 := by rcases hB z j with h|h <;> simp [h]
    have pp : p.natAbs ≤ 1 := by simpa [p,Int.natAbs_mul] using Nat.mul_le_mul ap bp
    have hx := Int.natAbs_add_le a p
    simp only [List.length_cons] at ha
    have hnew : (a+p).natAbs+zs.length ≤ m := by omega
    let t := s+3+((A i z).natAbs.size+(B z j).natAbs.size+1)^2+(a.natAbs.size+p.natAbs.size+1)^2
    have he : (dotGo A B i j (z::zs) a).run s = (dotGo A B i j zs (a+p)).run t := by
      simp only [dotGo,List.forIn_cons]; rfl
    rw [he]
    obtain ⟨hv,hc⟩ := ih (a+p) t hnew
    refine ⟨hv,hc.trans ?_⟩
    have sz (n:ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
    have h1 := Nat.pow_le_pow_left (by have := sz (A i z).natAbs; have := sz (B z j).natAbs; omega :
      (A i z).natAbs.size+(B z j).natAbs.size+1 ≤ 3) 2
    have h2 := Nat.pow_le_pow_left (by have := sz a.natAbs; have := sz p.natAbs; omega :
      a.natAbs.size+p.natAbs.size+1 ≤ m+2) 2
    dsimp [t]; simp only [List.length_cons,Nat.add_mul,one_mul]; omega

private theorem dotBudget {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A)
    (hB : ZeroOne B) (i j : Fin m) (zs : List (Fin m)) (hl : zs.length ≤ m) :
    Budget (dotGo A B i j zs 0) (fun c => c.natAbs ≤ m) (dotTime m) := by
  constructor; intro s
  obtain ⟨v,c⟩ := dotGo_bound A B hA hB i j zs 0 s (by simpa using hl)
  exact ⟨v,c.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : zs.length ≤ m+1)) _)⟩

private theorem readPush {α : Type} (z : α) {p : α → Prop} {a : Array α} {x : α}
    (h : ∀ i:ℕ, p (a[i]?.getD z)) (hx : p x) : ∀ i:ℕ, p ((a.push x)[i]?.getD z) := by
  intro i; rw [Array.getElem?_push]; split
  · exact hx
  · exact h i

private theorem poly_one_two (m : ℕ) (a b : ℤ) (ha : a.natAbs ≤ m) (hb : b.natAbs ≤ (m+1)^2)
    (flag : Prop) [Decidable flag] :
    polyFits (if flag then #[a,b] else #[a]) (width m) := by
  have h0 : 2 ≤ width m := by unfold width; nlinarith
  have h1 : m ≤ width m := by unfold width; nlinarith
  have h2 : (m+1)^2 ≤ width m := Nat.pow_le_pow_left (by omega) 2
  have hh := (Nat.lt_two_pow_self (n:=width m)).le
  by_cases h : flag <;> simp only [h,if_true,if_false] <;> constructor
  · exact h0
  · intro i; cases i with
    | zero => exact ha.trans (h1.trans hh)
    | succ i => cases i with
      | zero => exact hb.trans (h2.trans hh)
      | succ i => simp
  · change 1 ≤ _; omega
  · intro i; cases i with
    | zero => exact ha.trans (h1.trans hh)
    | succ i => simp

def weightTime (m : ℕ) := m*(2+100*(m+1)^3)
def matTime (m : ℕ) := m*((4*m+1)+m*(dotTime m+6)+1)

def weights {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (X Y : Finset (Fin m)) : Work (Array ℤ) :=
  forIn (List.finRange m) #[] fun i ws => do
    charge 2
    let x ← computeW A B X Y i
    return .yield (ws.push x)

def makeMat {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m) (zs : List (Fin m))
    (ws : Array ℤ) : Work (Array (Array ZPoly)) :=
  forIn (List.finRange m) #[] fun i mat => do
    charge (4*m+1)
    let row ← forIn (List.finRange m) (#[] : Array ZPoly) fun j row => do
      let c ← dotGo A B i j zs 0
      charge 6
      let p : ZPoly := if i=j ∧ i ≠ v then #[c, ws[i.val]?.getD 0] else #[c]
      return .yield (row.push p)
    charge 1
    return .yield (mat.push row)

theorem weights_budget {m} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (X Y : Finset (Fin m)) :
    Budget (weights A B X Y) (fun a => ∀ i:ℕ, (a[i]?.getD 0).natAbs ≤ (m+1)^2) (weightTime m) := by
  unfold weights weightTime
  apply bLe (bList (c:=2+100*(m+1)^3) (List.finRange m) _ _ (by simp) ?_) (by simp)
  intro i _ ws hws
  apply bTick
  constructor; intro s
  obtain ⟨hv,ht⟩ := computeW_bits A B hA hB X Y i s
  refine ⟨?_,ht⟩
  change ∀ j:ℕ, (((ws.push ((computeW A B X Y i).run s).1)[j]?).getD 0).natAbs ≤ (m+1)^2
  rw [hv]
  exact readPush 0 (p:=fun z:ℤ => z.natAbs ≤ (m+1)^2) hws (abs_weight A B hA hB X Y i)

theorem mat_budget {m} (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (zs : List (Fin m)) (hl : zs.length ≤ m) (ws : Array ℤ)
    (hws : ∀ i:ℕ, (ws[i]?.getD 0).natAbs ≤ (m+1)^2) :
    Budget (makeMat A B v zs ws) (fun a => matrixFits polyOps polyFits a (width m)) (matTime m) := by
  have hu : 1 ≤ width m := by unfold width; nlinarith
  have hnil : bufFits polyOps polyFits #[] (width m) := by
    intro i; simp [polyFits,polyOps]
  unfold makeMat matTime
  apply bLe (bList (c:=(4*m+1)+m*(dotTime m+6)+1) (List.finRange m) _ _ ?_ ?_) (by simp)
  · intro i; simpa using hnil
  · intro i _ mat hmat
    refine bLe (bTick (c:=m*(dotTime m+6)+1) ?_) (by omega)
    refine bLe (bBind (u:=m*(dotTime m+6)) (w:=1) (Q:=fun row => bufFits polyOps polyFits row (width m)) ?_ ?_) (by omega)
    · apply bLe (bList (c:=dotTime m+6) (List.finRange m) (fun r => bufFits polyOps polyFits r (width m)) #[] hnil ?_) (by simp)
      intro j _ row hrow
      apply bBind (dotBudget A B hA hB i j zs hl)
      intro c hc
      apply bTick (c:=0)
      exact bPure (bufPush hrow (poly_one_two m c _ hc (hws _) _))
    · intro row hrow
      apply bTick (c:=0)
      apply bPure
      exact readPush #[] (p:=fun r => bufFits polyOps polyFits r (width m)) hmat hrow

end EvaluationBudget

open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel Finset
namespace EvaluationBudget

def tailStep (m b : ℕ) := 2+(m+4)^2+(b+3)^2+(m+2*b+8)^2

def collectF (m k : ℕ) (Q : ZPoly) : Work ℤ :=
  forIn (List.range (min k m+1)) 0 fun q out => do
    charge 2
    let s ← paritySign (m-q+1)
    let a ← zmul s (Q[q]?.getD 0)
    let z ← zadd out a
    return .yield z

theorem collect_budget (m k : ℕ) (Q : ZPoly) (b : ℕ) (hQ : polyFits Q b) :
    Budget (collectF m k Q) (fun _ => True) ((m+1)*tailStep m b) := by
  apply bWeaken (bRange (c:=tailStep m b) (fun j (a:ℤ) => a.natAbs ≤ j*2^b) (by simp) ?_)
    (fun _ _ => trivial) (Nat.mul_le_mul_right _ (by omega : min k m+1 ≤ m+1))
  intro q hq z hz
  constructor; intro s
  let sig : ℤ := if (m-q+1)%2=0 then 1 else -1
  let x := Q[q]?.getD 0
  have habs : sig.natAbs=1 := by dsimp [sig]; split <;> decide
  have hx : x.natAbs ≤ 2^b := hQ.2 q
  have ha : (sig*x).natAbs=x.natAbs := by rw [Int.natAbs_mul,habs,one_mul]
  have hl : q ≤ 2^(m+1) := (show q ≤ m+1 by omega).trans Nat.lt_two_pow_self.le
  have zz : z.natAbs ≤ 2^(m+1+b) := by rw [pow_add]; exact hz.trans (Nat.mul_le_mul_right _ hl)
  have hsz := intBits zz
  have hsx := intBits hx
  constructor
  · change (z+sig*x).natAbs ≤ (q+1)*2^b
    exact (Int.natAbs_add_le _ _).trans (by rw [ha,Nat.add_mul,one_mul]; omega)
  · change s+2+((m-q+1).size+1)^2+(sig.natAbs.size+x.natAbs.size+1)^2+
      (z.natAbs.size+(sig*x).natAbs.size+1)^2 ≤ s+tailStep m b
    rw [ha,habs]
    have st : (m-q+1).size ≤ m-q+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have h1 := Nat.pow_le_pow_left (by omega : (m-q+1).size+1 ≤ m+4) 2
    have h2 := Nat.pow_le_pow_left (by change 1+x.natAbs.size+1 ≤ _; omega :
      (1:ℕ).size+x.natAbs.size+1 ≤ b+3) 2
    have h3 := Nat.pow_le_pow_left (by omega : z.natAbs.size+x.natAbs.size+1 ≤ m+2*b+8) 2
    unfold tailStep; omega

def fTime (m : ℕ) :=
  8*(m+1)^3 + ((4*m+1)+(weightTime m+
  ((4*m+1)+(matTime m+(determinantTime m (width m)+
  ((4*(m+1)+1)+((m+1)*tailStep m (cBound m (width m) m)+0)))))))

set_option maxHeartbeats 2000000 in
theorem computeF_budget (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ) (hA : ZeroOne A) (hB : ZeroOne B)
    (v : Fin m) (k : ℕ) (X Y : Finset (Fin m)) :
    Budget (computeF m A B v k X Y) (fun _ => True) (fTime m) := by
  let zs := ((X ∪ Y)ᶜ.sort (· ≤ ·))
  have hz : zs.length ≤ m := by simpa [zs] using Finset.card_le_univ ((X ∪ Y)ᶜ)
  let f : Work ℤ := do
    charge (8*(m+1)^3)
    charge (4*m+1)
    let ws ← weights A B X Y
    charge (4*m+1)
    let mat ← makeMat A B v zs ws
    let Q ← berkowitz polyOps m mat
    charge (4*(min k m+1)+1)
    let out ← collectF m k Q
    return out
  change Budget f _ _
  dsimp only [f,fTime]
  apply bTick
  apply bTick
  apply bBind (weights_budget A B hA hB X Y)
  intro ws hws
  apply bTick
  apply bBind (mat_budget A B hA hB v zs hz ws hws)
  intro mat hmat
  have hwidth : 1 ≤ width m := by unfold width; nlinarith
  apply bBind (uploaded_poly_determinant_budget mat m (width m) hwidth hmat)
  intro Q hQ
  apply bLe (bTick (c:=(m+1)*tailStep m (cBound m (width m) m)+0) ?_) (by omega)
  exact collect_budget m k Q _ hQ

end EvaluationBudget

open CapacitatedAssort.General BipHamCount.Deterministic BerkowitzModel EvaluationBudget
namespace EvaluationBudget
set_option maxHeartbeats 800000 in
theorem fTime_polynomial : ∃ K d : ℕ, ∀ m, fTime m ≤ K*(m+1)^d := by
  refine ⟨4419168867108828015, 20, fun m => ?_⟩
  unfold fTime width weightTime matTime dotTime tailStep determinantTime coefficientTime
    layerTime3 layerTime2 layerTime1 basicTime opCost cap cBound tBound vBound
  ring_nf
  omega
end EvaluationBudget

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℕ,
      ∀ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℤ), ZeroOne A → ZeroOne B →
        ∀ (v : Fin m) (k : ℕ), k ≤ m → ∀ X Y : Finset (Fin m),
          ((computeF m A B v k X Y).run 0).1 = Fval A B v k X Y ∧
          (((computeF m A B v k X Y).run 0).2 : ℝ) ≤ C * ((m : ℝ)+1)^c := by
  obtain ⟨K,d,h⟩ := fTime_polynomial
  refine ⟨(K+1:ℕ),by positivity,d,?_⟩
  intro m A B hA hB v k hk X Y
  refine ⟨computeF_correct A B v k hk X Y 0,?_⟩
  have cost := ((computeF_budget m A B hA hB v k X Y).run 0).2
  have coarse : ((computeF m A B v k X Y).run 0).2 ≤ (K+1)*(m+1)^d :=
    (by simpa using cost : ((computeF m A B v k X Y).run 0).2 ≤ fTime m) |>.trans
      ((h m).trans (Nat.mul_le_mul_right _ (by omega)))
  exact_mod_cast coarse
