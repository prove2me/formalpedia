-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.m_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T16:46:19.307377+00:00
-- url     : https://prove2.me/submissions/e46a453e-6bce-4855-bd2e-d6d00db7836f

import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Mathlib.Order.WellFounded
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

open DiscreteConvex.MConvexFunctions
open scoped BigOperators

namespace MIntegerOptimality
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem global_of_local (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x : V → ℤ) (hx : x ∈ DomZ f)
    (hloc : ∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w)) :
    ∀ y, f x ≤ f y := by
  classical
  intro y
  by_contra hbad
  have hy : f y < f x := lt_of_not_ge hbad
  let dist : (V → ℤ) → ℕ := fun z => (∑ w, |z w - x w|).toNat
  obtain ⟨z, hz, hmin⟩ := (measure dist).wf.has_min {z | f z < f x} ⟨y, hy⟩
  change f z < f x at hz
  have hzdom : z ∈ DomZ f := ne_top_of_lt hz
  have hzne : z ≠ x := by intro h; subst z; exact (lt_irrefl _ hz)
  have hpos : ∃ u : V, x u < z u := by
    by_contra hh
    push_neg at hh
    have hex : ∃ u : V, z u < x u := by
      by_contra hn
      push_neg at hn
      apply hzne
      funext u
      exact le_antisymm (hh u) (hn u)
    obtain ⟨u, hu⟩ := hex
    obtain ⟨v, hv, _⟩ := hf x hx z hzdom u (by simpa [SuppPos] using hu)
    have hv' : x v < z v := by simpa [SuppNeg] using hv
    exact (not_lt_of_ge (hh v)) hv'
  obtain ⟨u, hu⟩ := hpos
  obtain ⟨v, hv, hexc⟩ := hf z hzdom x hx u (by simpa [SuppPos] using hu)
  have hv' : z v < x v := by simpa [SuppNeg] using hv
  have huv : u ≠ v := by intro h; subst v; omega
  let z' : V → ℤ := fun w => z w - CharVec u w + CharVec v w
  let x' : V → ℤ := fun w => x w + CharVec u w - CharVec v w
  have hxloc : f x ≤ f x' := by
    convert hloc v u using 1
    congr 1
    funext w
    dsimp [x']
    ring
  have hzle : f z' ≤ f z := by
    have h : f z' + f x ≤ f z + f x :=
      (add_le_add_right hxloc (f z')).trans hexc
    exact (add_le_add_iff_left_of_ne_top hx).mp h
  have hdiff : (∑ w, |z' w - x w|) = (∑ w, |z w - x w|) - 2 := by
    have hp (w : V) : |z' w - x w| = |z w - x w| -
        (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
      by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, add_zero]
        rw [abs_of_nonneg (by omega : 0 ≤ z u - 1 - x u), abs_of_pos (by omega : 0 < z u - x u)]
        omega
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), sub_zero]
          rw [abs_of_nonpos (by omega : z v + 1 - x v ≤ 0), abs_of_neg (by omega : z v - x v < 0)]
          omega
        · simp [z', CharVec, hwu, hwv]
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
    ring
  apply hmin z' (hzle.trans_lt hz)
  change (∑ w, |z' w - x w|).toNat < (∑ w, |z w - x w|).toNat
  have hn : 0 ≤ ∑ w, |z' w - x w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (Int.toNat_lt_toNat (by omega : 0 < ∑ w, |z w - x w|)).mpr
  omega

def liftPoint (x : V → ℤ) : Option V → ℤ
  | none => -∑ v, x v
  | some v => x v

@[simp] theorem lift_value (f : (V → ℤ) → WithTop ℝ) (x : V → ℤ) :
    LiftedFunction f (liftPoint x) = f x := by simp [LiftedFunction, liftPoint]

theorem natural_global_of_local (f : (V → ℤ) → WithTop ℝ) (hf : MNaturalConvex f)
    (x : V → ℤ) (hx : x ∈ DomZ f)
    (hloc : ∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))
    (hpos : ∀ v : V, f x ≤ f (fun w => x w + CharVec v w))
    (hneg : ∀ v : V, f x ≤ f (fun w => x w - CharVec v w)) :
    ∀ y, f x ≤ f y := by
  classical
  have hR : ∀ u v : Option V, LiftedFunction f (liftPoint x) ≤
      LiftedFunction f (fun w => liftPoint x w - CharVec u w + CharVec v w) := by
    intro u v
    rw [lift_value]
    unfold LiftedFunction
    split_ifs
    · cases u with
      | none =>
        cases v with
        | none => simp [liftPoint]
        | some v => simpa [liftPoint, CharVec] using hpos v
      | some u =>
        cases v with
        | none => simpa [liftPoint, CharVec] using hneg u
        | some v => simpa [liftPoint, CharVec] using hloc u v
    · exact le_top
  have h := global_of_local (LiftedFunction f) hf (liftPoint x) (by simpa [DomZ] using hx) hR
  intro y
  simpa using h (liftPoint y)

end MIntegerOptimality

theorem solution {V : Type*} [Fintype V] [DecidableEq V] :
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔ (∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w))) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNaturalConvex f → ∀ x ∈ DomZ f,
      (∀ y, f x ≤ f y) ↔
        ((∀ u v : V, f x ≤ f (fun w => x w - CharVec u w + CharVec v w)) ∧
          (∀ v : V, f x ≤ f (fun w => x w + CharVec v w) ∧
            f x ≤ f (fun w => x w - CharVec v w)))) := by
  constructor
  · intro f hf x hx
    exact ⟨fun h u v => h _, MIntegerOptimality.global_of_local f hf x hx⟩
  · intro f hf x hx
    constructor
    · intro h
      exact ⟨fun u v => h _, fun v => ⟨h _, h _⟩⟩
    · rintro ⟨he, hp⟩
      exact MIntegerOptimality.natural_global_of_local f hf x hx he (fun v => (hp v).1) (fun v => (hp v).2)

#print axioms solution
