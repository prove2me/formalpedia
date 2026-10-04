-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.m_minimizer_cut
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T16:54:59.101109+00:00
-- url     : https://prove2.me/submissions/148c716d-d116-498a-9efa-a1946bc5cf8c

import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
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



open DiscreteConvex.MConvexFunctions
open scoped BigOperators

namespace MMinimizerCut
variable {V : Type*} [Fintype V] [DecidableEq V]

def distance (a z : V → ℤ) : ℕ := (∑ w, |z w - a w|).toNat

theorem exchange_closer (a z : V → ℤ) (u v : V)
    (hu : a u < z u) (hv : z v < a v) :
    distance a (fun w => z w - CharVec u w + CharVec v w) < distance a z := by
  classical
  have huv : u ≠ v := by intro h; subst v; omega
  let z' : V → ℤ := fun w => z w - CharVec u w + CharVec v w
  have hdiff : (∑ w, |z' w - a w|) = (∑ w, |z w - a w|) - 2 := by
    have hp (w : V) : |z' w - a w| = |z w - a w| -
        (if w = u then 1 else 0) - (if w = v then 1 else 0) := by
      by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, add_zero]
        rw [abs_of_nonneg (by omega : 0 ≤ z u - 1 - a u), abs_of_pos (by omega : 0 < z u - a u)]
        omega
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), sub_zero]
          rw [abs_of_nonpos (by omega : z v + 1 - a v ≤ 0), abs_of_neg (by omega : z v - a v < 0)]
          omega
        · simp [z', CharVec, hwu, hwv]
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
    ring
  change (∑ w, |z' w - a w|).toNat < (∑ w, |z w - a w|).toNat
  have hn : 0 ≤ ∑ w, |z' w - a w| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  apply (Int.toNat_lt_toNat (by omega : 0 < ∑ w, |z w - a w|)).mpr
  omega

theorem nearest_minimizer_cuts (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (hne : (ArgMin f).Nonempty) (a : V → ℤ) (ha : a ∈ DomZ f) :
    ∃ z ∈ ArgMin f,
      (∀ u : V, (∀ w : V, f a ≤ f (fun i => a i + CharVec u i - CharVec w i)) → z u ≤ a u) ∧
      (∀ v : V, (∀ w : V, f a ≤ f (fun i => a i - CharVec v i + CharVec w i)) → a v ≤ z v) := by
  classical
  obtain ⟨z, hz, hmin⟩ := (measure (distance a)).wf.has_min (ArgMin f) hne
  have hzdom : z ∈ DomZ f := ne_top_of_le_ne_top ha (hz a)
  refine ⟨z, hz, ?_, ?_⟩
  · intro u hloc
    by_contra hnot
    have hu : a u < z u := lt_of_not_ge hnot
    obtain ⟨v, hv, hexc⟩ := hf z hzdom a ha u (by simpa [SuppPos] using hu)
    have hv' : z v < a v := by simpa [SuppNeg] using hv
    let z' : V → ℤ := fun w => z w - CharVec u w + CharVec v w
    have hzle : f z' ≤ f z := by
      have h : f z' + f a ≤ f z + f a :=
        (add_le_add_right (hloc v) (f z')).trans hexc
      exact (add_le_add_iff_left_of_ne_top ha).mp h
    have hzmin : z' ∈ ArgMin f := fun y => hzle.trans (hz y)
    exact hmin z' hzmin (exchange_closer a z u v hu hv')
  · intro v hloc
    by_contra hnot
    have hv : z v < a v := lt_of_not_ge hnot
    obtain ⟨u, hu, hexc⟩ := hf a ha z hzdom v (by simpa [SuppPos] using hv)
    have hu' : a u < z u := by simpa [SuppNeg] using hu
    let z' : V → ℤ := fun w => z w - CharVec u w + CharVec v w
    have heq : (fun w => z w + CharVec v w - CharVec u w) = z' := by
      funext w; dsimp [z']; ring
    rw [heq] at hexc
    have hzle : f z' ≤ f z := by
      have h : f a + f z' ≤ f a + f z :=
        (add_le_add_left (hloc u) (f z')).trans hexc
      exact (add_le_add_iff_right_of_ne_top ha).mp h
    have hzmin : z' ∈ ArgMin f := fun y => hzle.trans (hz y)
    exact hmin z' hzmin (exchange_closer a z u v hu' hv)

end MMinimizerCut

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MExchangeAxiom f) (hne : (ArgMin f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMin f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMin f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) := by
  classical
  constructor
  · intro x hx v u hc
    let a : V → ℤ := fun w => x w - CharVec u w + CharVec v w
    have hax : f a ≤ f x := by simpa using hc v
    have ha : a ∈ DomZ f := ne_top_of_le_ne_top hx hax
    obtain ⟨z, hz, hcut, _⟩ := MMinimizerCut.nearest_minimizer_cuts f hf hne a ha
    refine ⟨z, hz, ?_⟩
    have h := hcut u (fun w => ?_)
    · simpa [a, CharVec] using h
    · convert hc w using 1
      congr 1; funext i; dsimp [a]; ring
  constructor
  · intro x hx u v hc
    let a : V → ℤ := fun w => x w - CharVec u w + CharVec v w
    have hax : f a ≤ f x := by simpa using hc u
    have ha : a ∈ DomZ f := ne_top_of_le_ne_top hx hax
    obtain ⟨z, hz, _, hcut⟩ := MMinimizerCut.nearest_minimizer_cuts f hf hne a ha
    refine ⟨z, hz, ?_⟩
    have h := hcut v (fun w => ?_)
    · simpa [a, CharVec] using h
    · convert hc w using 1
      congr 1; funext i; dsimp [a]; ring
  · intro x hx u v hc
    have huv : u ≠ v := by
      intro h; subst v
      apply hx.2
      apply MIntegerOptimality.global_of_local f hf x hx.1
      intro s t
      simpa using hc s t
    let a : V → ℤ := fun w => x w - CharVec u w + CharVec v w
    have hax : f a ≤ f x := by simpa using hc u u
    have ha : a ∈ DomZ f := ne_top_of_le_ne_top hx.1 hax
    obtain ⟨z, hz, hcutu, hcutv⟩ := MMinimizerCut.nearest_minimizer_cuts f hf hne a ha
    refine ⟨z, hz, ?_, ?_⟩
    · have h := hcutu u (fun w => ?_)
      · simpa [a, CharVec, huv] using h
      · convert hc w v using 1
        congr 1; funext i; dsimp [a]; ring
    · have h := hcutv v (fun w => ?_)
      · simpa [a, CharVec, Ne.symm huv] using h
      · convert hc u w using 1
        congr 1; funext i; dsimp [a]; ring

#print axioms solution
