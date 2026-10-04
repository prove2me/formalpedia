-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctions.m_proximity_theorem
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T17:20:49.502044+00:00
-- url     : https://prove2.me/submissions/3de4f5d4-2210-4b0a-b163-25246b717fd6

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNaturalConvex
import Mathlib.Order.WellFounded
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Order.Interval.Finset.Box
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Lemmas
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVecOpt


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



open DiscreteConvex.MConvexFunctions
open scoped BigOperators

namespace MProximityCore
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma strict_cost {a b c d : WithTop ℝ} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (hsum : c + d ≤ a + b) (hbd : b < d) : c < a := by
  obtain ⟨ra, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
  obtain ⟨rb, rfl⟩ := WithTop.ne_top_iff_exists.mp hb
  have hc : c ≠ ⊤ := by intro h; simp [h] at hsum
  have hd : d ≠ ⊤ := by intro h; simp [h] at hsum
  obtain ⟨rc, rfl⟩ := WithTop.ne_top_iff_exists.mp hc
  obtain ⟨rd, rfl⟩ := WithTop.ne_top_iff_exists.mp hd
  rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hsum
  rw [WithTop.coe_lt_coe] at hbd ⊢
  linarith

lemma finite_box (lo hi : V → ℤ) : (Set.Icc lo hi).Finite := by
  have h := Set.Finite.pi (fun v : V => Set.finite_Icc (lo v) (hi v))
  convert h using 1
  ext x
  simp [Set.mem_Icc, Set.mem_pi, Pi.le_def, forall_and]

def donorBox (x z : V → ℤ) (v : V) : Set (V → ℤ) :=
  {y | z v ≤ y v ∧ y v ≤ x v ∧
    (∀ w, w ≠ v → x w ≤ y w ∧ y w ≤ max (x w) (z w)) ∧
    ∑ w, y w = ∑ w, x w}

lemma donorBox_finite (x z : V → ℤ) (v : V) : (donorBox x z v).Finite := by
  classical
  apply (finite_box (fun w => if w = v then z w else x w)
    (fun w => if w = v then x w else max (x w) (z w))).subset
  intro y hy
  constructor <;> intro w <;> by_cases h : w = v
  · subst w; simpa using hy.1
  · simpa [h] using (hy.2.2.1 w h).1
  · subst w; simpa using hy.2.1
  · simpa [h] using (hy.2.2.1 w h).2

lemma donorBox_start (x z : V → ℤ) (v : V) (hv : z v ≤ x v) : x ∈ donorBox x z v := by
  exact ⟨hv, le_rfl, fun w _ => ⟨le_rfl, le_max_left _ _⟩, rfl⟩

lemma donorBox_down (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hvw : v ≠ w) (hv : z v < y v) (hw : y w < z w) :
    (fun i => y i - CharVec v i + CharVec w i) ∈ donorBox x z v := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [CharVec, eq_self, if_true, if_neg hvw, add_zero]; omega
  · simp only [CharVec, eq_self, if_true, if_neg hvw, add_zero]; linarith [hy.2.1]
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [CharVec, if_neg (Ne.symm hvw), eq_self, if_true, sub_zero]
      exact ⟨by linarith [(hy.2.2.1 w (Ne.symm hvw)).1],
        (show y w + 1 ≤ z w by omega).trans (le_max_right _ _)⟩
    · simpa [CharVec, hiv, hiw] using hy.2.2.1 i hiv
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [CharVec, hy.2.2.2]

lemma donorBox_up (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hvw : v ≠ w) (hv : y v < x v) (hw : x w < y w) :
    (fun i => y i + CharVec v i - CharVec w i) ∈ donorBox x z v := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [CharVec, eq_self, if_true, if_neg hvw, sub_zero]; linarith [hy.1]
  · simp only [CharVec, eq_self, if_true, if_neg hvw, sub_zero]; omega
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [CharVec, if_neg (Ne.symm hvw), eq_self, if_true, add_zero]
      exact ⟨by omega, by linarith [(hy.2.2.1 w (Ne.symm hvw)).2]⟩
    · simpa [CharVec, hiv, hiw] using hy.2.2.1 i hiv
  · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [CharVec, hy.2.2.2]

lemma donor_min_equal (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x z : V → ℤ) (c : WithTop ℝ) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ MMinimizerCut.distance x q < MMinimizerCut.distance x z)
    (v : V) (y : V → ℤ) (hy : y ∈ donorBox x z v) (hyd : y ∈ DomZ f)
    (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q) : y v = z v := by
  classical
  by_contra hnot
  have hv : z v < y v := lt_of_le_of_ne hy.1 (Ne.symm hnot)
  obtain ⟨w, hw, hexc⟩ := hf y hyd z hz v (by simpa [SuppPos] using hv)
  have hw' : y w < z w := by simpa [SuppNeg] using hw
  have hvw : v ≠ w := by intro heq; subst w; omega
  have hwx : x w < z w := (hy.2.2.1 w (Ne.symm hvw)).1.trans_lt hw'
  have hvx : z v < x v := hv.trans_le hy.2.1
  let z' : V → ℤ := fun i => z i + CharVec v i - CharVec w i
  have hcloser : MMinimizerCut.distance x z' < MMinimizerCut.distance x z := by
    convert MMinimizerCut.exchange_closer x z w v hwx hvx using 1
    congr 1; funext i; dsimp [z']; ring
  have hz' : c < f z' := lt_of_not_ge (fun h => hne z' h hcloser)
  have hy' := donorBox_down x z y v w hy hvw hv hw'
  have hlt := strict_cost hyd hz hexc (hzc.trans_lt hz')
  exact not_lt_of_ge (hmin _ hy') hlt

lemma receiver_le_deficit (x z y : V → ℤ) (v w : V)
    (hy : y ∈ donorBox x z v) (hwv : w ≠ v) : y w - x w ≤ x v - y v := by
  classical
  have hp (i : V) : (if i = v then y v - x v else 0) +
      (if i = w then y w - x w else 0) ≤ y i - x i := by
    by_cases hiv : i = v
    · subst i; simp [Ne.symm hwv]
    · by_cases hiw : i = w
      · subst i; simp [hwv]
      · simp only [if_neg hiv, if_neg hiw, zero_add]
        linarith [(hy.2.2.1 i hiv).1]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  rw [Finset.sum_sub_distrib, hy.2.2.2] at hs
  omega

def ray (x : V → ℤ) (v w : V) (m : ℤ) : V → ℤ :=
  fun i => x i - m * CharVec v i + m * CharVec w i

lemma ray_mem_box (x z y : V → ℤ) (v w : V) (hy : y ∈ donorBox x z v)
    (hwv : w ≠ v) (m : ℤ) (hm : 0 ≤ m) (hmw : m ≤ y w - x w) :
    ray x v w m ∈ donorBox x z v := by
  classical
  have hdef := receiver_le_deficit x z y v w hy hwv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ray, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), mul_one, mul_zero, add_zero]
    linarith [hy.1]
  · simp only [ray, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), mul_one, mul_zero, add_zero]
    omega
  · intro i hiv
    by_cases hiw : i = w
    · subst i
      simp only [ray, CharVec, if_neg hwv, eq_self, if_true, mul_zero, sub_zero, mul_one]
      exact ⟨by omega, (show x w + m ≤ y w by omega).trans (hy.2.2.1 w hwv).2⟩
    · simpa [ray, CharVec, hiv, hiw] using (show x i ≤ x i ∧ x i ≤ max (x i) (z i) from ⟨le_rfl, le_max_left _ _⟩)
  · simp only [ray, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [CharVec]

lemma box_min_strict_above (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x z : V → ℤ) (c : WithTop ℝ) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ MMinimizerCut.distance x q < MMinimizerCut.distance x z)
    (v : V) (y : V → ℤ) (hyd : y ∈ DomZ f)
    (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q)
    (q : V → ℤ) (hq : q ∈ donorBox x z v) (hqv : z v < q v) : f y < f q := by
  by_contra hnot
  have hqy : f q ≤ f y := le_of_not_gt hnot
  have hqd : q ∈ DomZ f := ne_top_of_le_ne_top hyd hqy
  have hqmin : ∀ r ∈ donorBox x z v, f q ≤ f r := fun r hr => hqy.trans (hmin r hr)
  have heq := donor_min_equal f hf x z c hz hzc hne v q hq hqd hqmin
  omega

lemma receiver_lt_scale (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ MMinimizerCut.distance x q < MMinimizerCut.distance x z)
    (v : V) (hv : z v < x v) (y : V → ℤ) (hy : y ∈ donorBox x z v)
    (hyd : y ∈ DomZ f) (hmin : ∀ q ∈ donorBox x z v, f y ≤ f q)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (w : V) (hwv : w ≠ v) : y w - x w ≤ alpha - 1 := by
  classical
  have hyv : y v = z v := donor_min_equal f hf x z c hz hzc hne v y hy hyd hmin
  by_contra hnot
  have hcap : alpha ≤ y w - x w := by omega
  have hwy : x w < y w := by omega
  let yup : V → ℤ := fun i => y i + CharVec v i - CharVec w i
  have hup : yup ∈ donorBox x z v := donorBox_up x z y v w hy (Ne.symm hwv) (by omega) hwy
  have hupy : f y < f yup := box_min_strict_above f hf x z c hz hzc hne v y hyd hmin yup hup
    (by simp only [yup, CharVec, eq_self, if_true, if_neg (Ne.symm hwv), sub_zero]; omega)
  have step (m : ℕ) (hm : (m : ℤ) < y w - x w)
      (hr : ray x v w m ∈ DomZ f) : f (ray x v w ((m : ℤ) + 1)) < f (ray x v w m) := by
    have hww : (ray x v w m) w < y w := by simp [ray, CharVec, hwv]; omega
    obtain ⟨i, hi, hexc⟩ := hf y hyd (ray x v w m) hr w (by simpa [SuppPos] using hww)
    have hi' : y i < (ray x v w m) i := by simpa [SuppNeg] using hi
    have hiv : i = v := by
      by_contra hiv
      by_cases hiw : i = w
      · subst i; omega
      · have hh := (hy.2.2.1 i hiv).1
        simp only [ray, CharVec, if_neg hiv, if_neg hiw, mul_zero, sub_zero, add_zero] at hi'
        omega
    subst i
    have heq1 : (fun i => y i - CharVec w i + CharVec v i) = yup := by
      funext i; dsimp [yup]; ring
    have heq2 : (fun i => ray x v w m i + CharVec w i - CharVec v i) =
        ray x v w ((m : ℤ) + 1) := by funext i; dsimp [ray]; ring
    rw [heq1, heq2] at hexc
    exact strict_cost hr hyd (by simpa only [add_comm] using hexc) hupy
  have ray_values : ∀ m : ℕ, (m : ℤ) ≤ y w - x w →
      f (ray x v w m) ≤ f x ∧ (0 < m → f (ray x v w m) < f x) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.cast_zero]
      have hzero : ray x v w 0 = x := by funext i; simp [ray]
      rw [hzero]
      exact ⟨le_rfl, by omega⟩
    | succ m ih =>
      intro hm
      obtain ⟨hprev, _⟩ := ih (by omega)
      have hrd : ray x v w m ∈ DomZ f := ne_top_of_le_ne_top hx hprev
      have hs := step m (by omega) hrd
      have hs' : f (ray x v w (m + 1 : ℕ)) < f x := by
        simpa only [Nat.cast_add, Nat.cast_one] using hs.trans_le hprev
      exact ⟨hs'.le, fun _ => hs'⟩
  have hval := (ray_values alpha.toNat (by omega)).2 (by omega)
  have hval' : f (ray x v w alpha) < f x := by simpa [Int.toNat_of_nonneg ha.le] using hval
  have hlocal : f x ≤ f (ray x v w alpha) := by
    convert hloc v w using 1
    congr 1; funext i; dsimp [ray]; ring
  exact not_lt_of_ge hlocal hval'

lemma donor_bound (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ MMinimizerCut.distance x q < MMinimizerCut.distance x z)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (v : V) : x v - z v ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  classical
  have hcpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  by_cases hv : z v < x v
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (donorBox x z v) f (donorBox_finite x z v)
      ⟨x, donorBox_start x z v hv.le⟩
    have hyd : y ∈ DomZ f := ne_top_of_le_ne_top hx (hmin x (donorBox_start x z v hv.le))
    have hyv : y v = z v := donor_min_equal f hf x z c hz hzc hne v y hy hyd hmin
    have hb (w : V) (hwv : w ≠ v) : y w - x w ≤ alpha - 1 :=
      receiver_lt_scale f hf x z c hx hz hzc hne v hv y hy hyd hmin alpha ha hloc w hwv
    have hsum := Finset.sum_erase_add (s := Finset.univ) (fun w => y w - x w) (Finset.mem_univ v)
    have hs0 : (∑ w : V, (y w - x w)) = 0 := by rw [Finset.sum_sub_distrib, hy.2.2.2, sub_self]
    rw [hs0] at hsum
    have hle := Finset.sum_le_sum (s := Finset.univ.erase v)
      (fun w hw => hb w (Finset.mem_erase.mp hw).1)
    have hc : ((Finset.univ.erase v).card : ℤ) + 1 = (Fintype.card V : ℤ) := by
      exact_mod_cast Finset.card_erase_add_one (s := Finset.univ) (Finset.mem_univ v)
    simp only [Finset.sum_const, nsmul_eq_mul] at hle
    have hc' : ((Finset.univ.erase v).card : ℤ) = (Fintype.card V : ℤ) - 1 := by omega
    rw [hc'] at hle
    rw [hyv] at hsum
    linarith
  · have hb : 0 ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := mul_nonneg (by omega) (by omega)
    omega

lemma exchange_neg (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f) :
    MExchangeAxiom (fun x => f (fun w => -x w)) := by
  classical
  intro x hx y hy u hu
  have hu' : (fun w => -x w) u < (fun w => -y w) u := by
    have h : y u < x u := by simpa [SuppPos] using hu
    change -x u < -y u
    omega
  obtain ⟨v, hv, hh⟩ := hf (fun w => -y w) hy (fun w => -x w) hx u
    (by simpa [SuppPos] using hu')
  have hv' : x v < y v := by
    have h : -y v < -x v := by simpa [SuppNeg] using hv
    omega
  refine ⟨v, by simpa [SuppNeg] using hv', ?_⟩
  have heq1 : (fun w => -(x w - CharVec u w + CharVec v w)) =
      (fun w => -x w + CharVec u w - CharVec v w) := by funext w; ring
  have heq2 : (fun w => -(y w + CharVec u w - CharVec v w)) =
      (fun w => -y w - CharVec u w + CharVec v w) := by funext w; ring
  change f (fun w => -(x w - CharVec u w + CharVec v w)) +
    f (fun w => -(y w + CharVec u w - CharVec v w)) ≤ f (fun w => -x w) + f (fun w => -y w)
  rw [heq1, heq2]
  simpa only [add_comm] using hh

lemma distance_neg (a z : V → ℤ) :
    MMinimizerCut.distance (fun w => -a w) (fun w => -z w) = MMinimizerCut.distance a z := by
  unfold MMinimizerCut.distance
  have hp (w : V) : -z w - -a w = -(z w - a w) := by ring
  simp_rw [hp, abs_neg]

lemma receiver_bound (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (x z : V → ℤ) (c : WithTop ℝ) (hx : x ∈ DomZ f) (hz : z ∈ DomZ f) (hzc : f z ≤ c)
    (hne : ∀ q, f q ≤ c → ¬ MMinimizerCut.distance x q < MMinimizerCut.distance x z)
    (alpha : ℤ) (ha : 0 < alpha)
    (hloc : ∀ u w : V, f x ≤ f (fun i => x i + alpha * (CharVec w i - CharVec u i)))
    (v : V) : z v - x v ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  let g : (V → ℤ) → WithTop ℝ := fun q => f (fun i => -q i)
  let nx : V → ℤ := fun i => -x i
  let nz : V → ℤ := fun i => -z i
  have hg : MExchangeAxiom g := exchange_neg f hf
  have hxg : nx ∈ DomZ g := by simpa [DomZ, g, nx] using hx
  have hzg : nz ∈ DomZ g := by simpa [DomZ, g, nz] using hz
  have hzcg : g nz ≤ c := by simpa [g, nz] using hzc
  have hneg : ∀ q, g q ≤ c → ¬ MMinimizerCut.distance nx q < MMinimizerCut.distance nx nz := by
    intro q hq hh
    apply hne (fun w => -q w) hq
    have hqdist := distance_neg x (fun w => -q w)
    simp only [neg_neg] at hqdist
    change MMinimizerCut.distance (fun w => -x w) q <
      MMinimizerCut.distance (fun w => -x w) (fun w => -z w) at hh
    rwa [hqdist, distance_neg] at hh
  have hlocg : ∀ u w : V, g nx ≤ g (fun i => nx i + alpha * (CharVec w i - CharVec u i)) := by
    intro u w
    dsimp only [g, nx]
    simp only [neg_neg]
    convert hloc w u using 1
    congr 1; funext i; ring
  have h := donor_bound g hg nx nz c hxg hzg hzcg hneg alpha ha hlocg v
  dsimp only [nx, nz] at h
  linarith

end MProximityCore


open DiscreteConvex.MConvexFunctions
open scoped BigOperators

namespace MProximityFinal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem m_proximity (f : (V → ℤ) → WithTop ℝ) (hf : MExchangeAxiom f)
    (alpha : ℤ) (ha : 0 < alpha) (x : V → ℤ) (hx : x ∈ DomZ f)
    (hloc : ∀ u v : V, f x ≤ f (fun w => x w + alpha * (CharVec v w - CharVec u w))) :
    (ArgMin f).Nonempty ∧ ∃ z ∈ ArgMin f,
      ∀ v : V, |x v - z v| ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1) := by
  classical
  let B : ℤ := ((Fintype.card V : ℤ) - 1) * (alpha - 1)
  let S : Set (V → ℤ) := Set.Icc (fun v => x v - B) (fun v => x v + B)
  have hB (v : V) : 0 ≤ B := by
    have hc : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    exact mul_nonneg (by omega) (by omega)
  have hxS : x ∈ S := by
    constructor
    · intro v
      change x v - B ≤ x v
      have h := hB v
      omega
    · intro v
      change x v ≤ x v + B
      have h := hB v
      omega
  have hSf : S.Finite := MProximityCore.finite_box _ _
  obtain ⟨a, haS, hamin⟩ := Set.exists_min_image S f hSf ⟨x, hxS⟩
  have hag : a ∈ ArgMin f := by
    intro y
    by_contra hnot
    have hya : f y < f a := lt_of_not_ge hnot
    have haf : a ∈ DomZ f := ne_top_of_le_ne_top hx (hamin x hxS)
    have hyf : y ∈ DomZ f := ne_top_of_lt hya
    obtain ⟨z, hz, hn⟩ := (measure (MMinimizerCut.distance x)).wf.has_min {q | f q ≤ f y} ⟨y, by change f y ≤ f y; exact le_rfl⟩
    change f z ≤ f y at hz
    have hzf : z ∈ DomZ f := ne_top_of_le_ne_top hyf hz
    have hzS : z ∈ S := by
      constructor <;> intro v
      · have h := MProximityCore.donor_bound f hf x z (f y) hx hzf hz hn alpha ha hloc v
        change x v - B ≤ z v
        dsimp [B]; linarith
      · have h := MProximityCore.receiver_bound f hf x z (f y) hx hzf hz hn alpha ha hloc v
        change z v ≤ x v + B
        dsimp [B]; linarith
    exact (not_lt_of_ge ((hamin z hzS).trans hz)) hya
  refine ⟨⟨a, hag⟩, a, hag, ?_⟩
  intro v
  have hlo := haS.1 v
  have hhi := haS.2 v
  change x v - B ≤ a v at hlo
  change a v ≤ x v + B at hhi
  change |x v - a v| ≤ B
  rw [abs_le]
  constructor <;> omega

end MProximityFinal

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (alpha : ℤ) (halpha : 0 < alpha) :
    (∀ f : (V → ℤ) → WithTop ℝ, MExchangeAxiom f → ∀ xalpha ∈ DomZ f,
        (∀ u v : V, f xalpha ≤ f (fun w => xalpha w + alpha * (CharVec v w - CharVec u w))) →
        (ArgMin f).Nonempty ∧
          ∃ x ∈ ArgMin f, ∀ v : V, |xalpha v - x v| ≤ ((Fintype.card V : ℤ) - 1) * (alpha - 1)) ∧
    (∀ f : (V → ℤ) → WithTop ℝ, MNaturalConvex f → ∀ xalpha ∈ DomZ f,
        (∀ u v : Option V,
            f xalpha ≤ f (fun w => xalpha w + alpha * (CharVecOpt v w - CharVecOpt u w))) →
        (ArgMin f).Nonempty ∧
          ∃ x ∈ ArgMin f, ∀ v : V, |xalpha v - x v| ≤ (Fintype.card V : ℤ) * (alpha - 1)) := by
  classical
  constructor
  · intro f hf x hx hloc
    exact MProximityFinal.m_proximity f hf alpha halpha x hx hloc
  · intro f hf x hx hloc
    have hxL : MIntegerOptimality.liftPoint x ∈ DomZ (LiftedFunction f) := by
      simpa [DomZ] using hx
    have hlocL : ∀ u v : Option V,
        LiftedFunction f (MIntegerOptimality.liftPoint x) ≤ LiftedFunction f
          (fun w => MIntegerOptimality.liftPoint x w + alpha * (CharVec v w - CharVec u w)) := by
      intro u v
      rw [MIntegerOptimality.lift_value]
      unfold LiftedFunction
      split_ifs
      · cases u with
        | none =>
          cases v with
          | none => simpa [MIntegerOptimality.liftPoint, CharVec, CharVecOpt] using hloc none none
          | some v => simpa [MIntegerOptimality.liftPoint, CharVec, CharVecOpt] using hloc none (some v)
        | some u =>
          cases v with
          | none => simpa [MIntegerOptimality.liftPoint, CharVec, CharVecOpt] using hloc (some u) none
          | some v => simpa [MIntegerOptimality.liftPoint, CharVec, CharVecOpt] using hloc (some u) (some v)
      · exact le_top
    obtain ⟨_, z, hz, hbound⟩ := MProximityFinal.m_proximity (LiftedFunction f) hf alpha halpha
      (MIntegerOptimality.liftPoint x) hxL hlocL
    have hzfin : LiftedFunction f z ≠ ⊤ := ne_top_of_le_ne_top hxL (hz (MIntegerOptimality.liftPoint x))
    have hzval : LiftedFunction f z = f (fun v => z (some v)) := by
      unfold LiftedFunction at hzfin ⊢
      split_ifs <;> simp_all
    have hmin : (fun v => z (some v)) ∈ ArgMin f := by
      intro y
      have h := hz (MIntegerOptimality.liftPoint y)
      simpa only [hzval, MIntegerOptimality.lift_value] using h
    refine ⟨⟨_, hmin⟩, _, hmin, ?_⟩
    intro v
    have h := hbound (some v)
    simpa [MIntegerOptimality.liftPoint] using h

#print axioms solution
