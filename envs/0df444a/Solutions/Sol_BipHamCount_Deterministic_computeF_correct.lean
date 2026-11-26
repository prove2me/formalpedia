-- Prove2me | solution 1 for BipHamCount.Deterministic.computeF_correct
-- status  : ACCEPTED   (prove)
-- author  : @Soh Kumabe
-- created : 2026-11-26T10:23:50.62315+00:00
-- url     : https://prove2.me/submissions/1d96ee63-26c9-40e4-801f-d6e1f6ed314c

import Theorems.Thm_BipHamCount_Deterministic_berkowitz_det_correct
import Definitions.Def_BipHamCount_Deterministic_Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.FinRange
import Definitions.Def_BipHamCount_Deterministic_Programs
import Theorems.Thm_BipHamCount_Deterministic_Fval_det_coeff

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

end BerkowitzModel

namespace BerkowitzModel
open CapacitatedAssort.General

theorem ofFnPost {α β : Type} {n : ℕ} (f : Fin n → α) (I : ℕ → β → Prop)
    (p : α → β → Work (ForInStep β)) (b : β) (h : I 0 b)
    (step : ∀ i (s : β), I i.val s → Post (p (f i) s) (Yield (I (i.val+1)))) :
    Post (forIn (List.ofFn f) b p) (I n) := by
  induction n generalizing b I with
  | zero => rw [List.ofFn_zero,List.forIn_nil]; exact purePost h
  | succ n ih =>
    rw [List.ofFn_succ,List.forIn_cons]
    apply bindPost (step 0 b h)
    intro z hz
    cases z with
    | done _ => exact False.elim hz
    | yield z =>
      apply ih (fun i => f i.succ) (fun k => I (k+1)) z hz
      intro i s hs
      exact step i.succ s hs

structure FinPrefix {α : Type} {m : ℕ} (a : Array α) (d : α) (n : ℕ)
    (f : Fin m → α → Prop) : Prop where
  size : a.size = n
  atLt : ∀ i : Fin m, i.val < n → f i (a[i.val]?.getD d)

theorem pushFin {α : Type} {m : ℕ} {a : Array α} {d x : α} {i : Fin m} {f : Fin m → α → Prop}
    (ha : FinPrefix a d i.val f) (hx : f i x) : FinPrefix (a.push x) d (i.val+1) f := by
  refine ⟨by simp [ha.size],?_⟩
  intro j hj
  rw [Array.getElem?_push,ha.size]
  by_cases he : j = i
  · subst j; simpa using hx
  · rw [if_neg (by exact fun h => he (Fin.ext h))]
    exact ha.atLt j (by have := Fin.val_ne_of_ne he; omega)

theorem finArrayPost {α : Type} {m : ℕ} (d : α) (f : Fin m → α → Prop)
    (p : Fin m → Array α → Work (ForInStep (Array α)))
    (step : ∀ i a, FinPrefix a d i.val f → Post (p i a) (Yield (fun b => FinPrefix b d (i.val+1) f))) :
    Post (forIn (List.finRange m) #[] p) (fun out => FinPrefix out d m f) := by
  apply ofFnPost (fun i => i) (fun k b => FinPrefix b d k f) p #[] ?_ step
  exact ⟨rfl,fun _ h => (Nat.not_lt_zero _ h).elim⟩

end BerkowitzModel
namespace BerkowitzModel
open Finset Polynomial BipHamCount.Deterministic
open scoped Polynomial
noncomputable def polyEval (a : ZPoly) : ℤ[X] :=
  ∑ i ∈ range a.size, monomial i (a[i]?.getD 0)

end BerkowitzModel

open BipHamCount.Deterministic BerkowitzModel CapacitatedAssort.General Polynomial Finset
open scoped BigOperators Polynomial

private lemma addList {ι : Type} (L : List ι) (f : ι → ℤ) (p : ι → ℤ → Work (ForInStep ℤ))
    (h : ∀ j z, Post (p j z) (· = .yield (z + f j))) (a : ℤ) :
    Post (forIn L a p) (fun out => out = a+(L.map f).sum) := by
  induction L generalizing a with
  | nil => rw [List.forIn_nil]; apply purePost; simp
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply bindPost (h x a)
    intro z hz
    subst z
    apply postMono (ih _)
    intro y hy; simpa [add_assoc] using hy

private lemma sortSum {m : ℕ} (X : Finset (Fin m)) (f : Fin m → ℤ) :
    ((X.sort (· ≤ ·)).map f).sum = ∑ j ∈ X, f j :=
  ((X.sort_perm_toList (· ≤ ·)).map f).sum_eq.trans (X.sum_map_toList f)

private lemma wRun {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (U V : Finset (Fin m)) (i : Fin m) :
    Post (computeW A B U V i) (· = w A B U V i) := by
  rw [computeW]
  apply tickPost
  apply bindPost (addList _ (A i) _ (fun _ _ => ⟨fun _ => rfl⟩) 0)
  intro a ha
  apply bindPost (addList _ (fun j => B j i) _ (fun _ _ => ⟨fun _ => rfl⟩) 0)
  intro b hb
  constructor
  intro s
  change a*b = _
  simp [ha,hb,sortSum,w]

private lemma parityRun (n : ℕ) : Post (paritySign n) (· = (-1 : ℤ)^n) := by
  constructor
  intro s
  change (if n%2 = 0 then 1 else -1) = _
  split
  next h => rw [(Nat.even_iff.mpr h).neg_one_pow]
  next h => rw [(Nat.not_even_iff_odd.mp (fun k => h (Nat.even_iff.mp k))).neg_one_pow]

private lemma poly_const (c : ℤ) : polyEval #[c] = C c := by simp [polyEval]
private lemma poly_linear (c d : ℤ) : polyEval #[c,d] = C c + C d * X := by
  simp [polyEval,Finset.sum_range_succ]
  exact Polynomial.C_mul_X_eq_monomial.symm

theorem computeF_value {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (hk : k ≤ m) (U V : Finset (Fin m)) :
    Post (computeF m A B v k U V) (· = Fval A B v k U V) := by
  classical
  let Z := (U ∪ V)ᶜ
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j => ∑ z ∈ Z, A i z * B z j
  let D : Matrix (Fin m) (Fin m) ℤ[X] := Matrix.diagonal
    (fun i => if i ≠ v then C (w A B U V i) * X else 0) + M.map C
  let expected (i j : Fin m) : ZPoly := if i=j ∧ i≠v then #[M i j,w A B U V i] else #[M i j]
  rw [computeF]
  apply tickPost
  apply tickPost
  apply bindPost (Q := fun ws => FinPrefix ws 0 m (fun i e => e = w A B U V i))
  · apply finArrayPost
    intro i xs hxs
    apply tickPost
    apply bindPost (wRun A B U V i)
    intro x hx
    exact purePost (pushFin hxs hx)
  intro ws hws
  apply tickPost
  apply bindPost (Q := fun mat => FinPrefix mat #[] m (fun i row =>
    FinPrefix row #[] m (fun j e => e = expected i j)))
  · apply finArrayPost
    intro i mat hmat
    apply tickPost
    apply bindPost (Q := fun row => FinPrefix row #[] m (fun j e => e = expected i j))
    · apply finArrayPost
      intro j row hrow
      apply bindPost (addList _ (fun z => A i z * B z j) _ (fun z acc => ⟨fun _ => rfl⟩) 0)
      intro c hc
      apply tickPost
      apply purePost
      apply pushFin hrow
      simp only [zero_add,sortSum] at hc
      simp [expected, hc, M,Z,hws.atLt i i.isLt]
    intro row hrow
    apply tickPost
    exact purePost (pushFin hmat hrow)
  intro mat hmat
  let packed : Matrix (Fin m) (Fin m) ℤ[X] := fun i j => polyEval (((mat[i.val]?.getD #[])[j.val]?).getD #[])
  have he : packed = D := by
    apply Matrix.ext
    intro i j
    change polyEval (((mat[i.val]?.getD #[])[j.val]?).getD #[]) = D i j
    rw [(hmat.atLt i i.isLt).atLt j j.isLt]
    by_cases hij : i=j
    · subst j
      by_cases hv : i=v
      · simp [expected,hv,D,Matrix.map_apply,poly_const]
      · simp [expected,hv,D,Matrix.map_apply,poly_linear,add_comm]
    · simp [expected,hij,D,Matrix.map_apply,poly_const]
  have hb : Post (berkowitz polyOps m mat) (fun q => ∀ i, q[i]?.getD 0 = D.det.coeff i) := by
    constructor
    intro s i
    have hq := berkowitz_det_correct.2 mat m s i
    change _ = packed.det.coeff i at hq
    rwa [he] at hq
  apply bindPost hb
  intro q hq
  apply tickPost
  let term := fun d => (-1 : ℤ)^(m-d+1)*D.det.coeff d
  apply bindPost (Q := fun a => a = ∑ d ∈ range (min k m+1), term d)
  · apply rangePost (fun l (a : ℤ) => a = ∑ d ∈ range l, term d)
    · simp
    · intro d hd a ha
      apply tickPost
      apply bindPost (parityRun _)
      intro s hs
      constructor
      intro cost
      change a + s * q[d]?.getD 0 = _
      rw [ha,hs, hq, Finset.sum_range_succ]
  intro out hout
  apply purePost
  rw [hout,min_eq_left hk]
  exact Fval_det_coeff A B v k U V
theorem solution {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℤ) (v : Fin m)
    (k : ℕ) (hk : k ≤ m) (U V : Finset (Fin m)) (s : ℕ) :
    ((computeF m A B v k U V).run s).1 = Fval A B v k U V := (computeF_value A B v k hk U V).run s
