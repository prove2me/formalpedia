-- Prove2me | solution 1 for DiscreteConvex.MConvexFunctionsD.polyhedral_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T15:55:58.622157+00:00
-- url     : https://prove2.me/submissions/085e5128-e575-480f-9354-ea343cd5b4a4

import Definitions.Def_DiscreteConvex_MConvexFunctionsD_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomR
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DirDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Finset.Max
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MExchangeAxiomR
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FunProp
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_MNaturalConvexR



open DiscreteConvex.MConvexFunctionsD
namespace PolyhedralSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem finite_positive_bound {I : Type*} [DecidableEq I] (s : Finset I)
    (f : I → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i ∈ s, e ≤ f i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨e, he, hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    refine ⟨min e (f i), lt_min he (hf i (Finset.mem_insert_self _ _)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hbound j hj)

def epiPoint (p : V → ℝ) (r : ℝ) : Option V → ℝ
  | none => r
  | some v => p v

@[simp] theorem row_epi (a : Option V → ℝ) (p : V → ℝ) (r : ℝ) :
    (∑ w, a w * epiPoint p r w) = a none * r + ∑ v, a (some v) * p v := by
  simp [Fintype.sum_option, epiPoint]

theorem exists_affine_minorant (g : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex g) (p : V → ℝ) (hp : g p ≠ ⊤) :
    ∃ a : V → ℝ, ∀ q : V → ℝ,
      g p + ((∑ v, a v * (q v - p v) : ℝ) : WithTop ℝ) ≤ g q := by
  classical
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hp
  obtain ⟨m, a, b, hab⟩ := hpoly
  have hrep (q : V → ℝ) (s : ℝ) :
      g q ≤ (s : WithTop ℝ) ↔
        ∀ i, a i none * s + ∑ v, a i (some v) * q v ≤ b i := by
    have h := Set.ext_iff.mp hab (epiPoint q s)
    change g q ≤ (s : WithTop ℝ) ↔ (∀ i, ∑ w, a i w * epiPoint q s w ≤ b i) at h
    simpa only [row_epi] using h
  have hrow : ∀ i, a i none * r + ∑ v, a i (some v) * p v ≤ b i :=
    (hrep p r).mp (le_of_eq hr.symm)
  have hactive : ∃ i, a i none < 0 ∧
      a i none * r + ∑ v, a i (some v) * p v = b i := by
    by_contra h
    push_neg at h
    let f : Fin m → ℝ := fun i => if a i none < 0 then
      (b i - (a i none * r + ∑ v, a i (some v) * p v)) / (-a i none) else 1
    have hf : ∀ i, 0 < f i := by
      intro i
      dsimp [f]
      split_ifs with ha
      · exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hrow i) (h i ha))) (neg_pos.mpr ha)
      · norm_num
    obtain ⟨e, he, heBound⟩ := finite_positive_bound Finset.univ f (fun i _ => hf i)
    have hlower : g p ≤ ((r - e : ℝ) : WithTop ℝ) := by
      apply (hrep p (r-e)).mpr
      intro i
      by_cases ha : a i none < 0
      · have hb := heBound i (Finset.mem_univ i)
        simp only [f, if_pos ha] at hb
        have hc := (le_div_iff₀ (neg_pos.mpr ha)).mp hb
        nlinarith
      · have hc : 0 ≤ a i none := le_of_not_gt ha
        have hd := mul_nonneg hc (le_of_lt he)
        nlinarith [hrow i]
    rw [← hr, WithTop.coe_le_coe] at hlower
    linarith
  obtain ⟨i, hi, htight⟩ := hactive
  let d : ℝ := -a i none
  have hd : 0 < d := neg_pos.mpr hi
  refine ⟨fun v => a i (some v) / d, ?_⟩
  intro q
  by_cases hq : g q = ⊤
  · simp [hq]
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hq
  have hrowq := (hrep q s).mp (le_of_eq hs.symm) i
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe]
  have hsum : (∑ v, a i (some v) / d * (q v - p v)) =
      ((∑ v, a i (some v) * q v) - ∑ v, a i (some v) * p v) / d := by
    simp only [div_mul_eq_mul_div, mul_sub, sub_div, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hsum]
  have hquot : ((∑ v, a i (some v) * q v) - ∑ v, a i (some v) * p v) / d ≤ s-r := by
    apply (div_le_iff₀ hd).mpr
    dsimp [d]
    nlinarith
  linarith

#print axioms exists_affine_minorant
end PolyhedralSupport


open DiscreteConvex.MConvexFunctionsD
namespace PolyhedralDirectional
variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem scalar_coe (c r : ℝ) :
    PosScalarMul c (r : WithTop ℝ) = ((c*r : ℝ) : WithTop ℝ) := rfl

@[simp] theorem scalar_top (c : ℝ) (hc : c ≠ 0) :
    PosScalarMul c (⊤ : WithTop ℝ) = ⊤ := by simp [PosScalarMul, hc]

theorem quotient_nonneg_iff (x y : WithTop ℝ) (hx : x ≠ ⊤) (t : ℝ) (ht : 0 < t) :
    0 ≤ PosScalarMul (1/t) (y-x) ↔ x ≤ y := by
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.mp hx
  by_cases hy : y = ⊤
  · simp [hy, ne_of_gt ht]
  obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.mp hy
  rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, scalar_coe]
  rw [← WithTop.coe_zero, WithTop.coe_le_coe, WithTop.coe_le_coe]
  rw [mul_nonneg_iff_of_pos_left (one_div_pos.mpr ht), sub_nonneg]

theorem quotient_bddBelow (g : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex g) (p d : V → ℝ) (hp : g p ≠ ⊤) :
    BddBelow {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
      L = PosScalarMul (1 / t) (g (fun v => p v + t*d v) - g p)} := by
  obtain ⟨a, ha⟩ := PolyhedralSupport.exists_affine_minorant g hpoly p hp
  refine ⟨((∑ v, a v*d v : ℝ) : WithTop ℝ), ?_⟩
  rintro L ⟨t, ht, rfl⟩
  by_cases hq : g (fun v => p v + t*d v) = ⊤
  · simp [hq, ne_of_gt ht]
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hp
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hq
  have hbound := ha (fun v => p v + t*d v)
  rw [← hr, ← hs, ← WithTop.coe_add, WithTop.coe_le_coe] at hbound
  have hsum : (∑ v, a v*(p v+t*d v-p v)) = t * ∑ v, a v*d v := by
    simp only [add_sub_cancel_left]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hsum] at hbound
  rw [← hr, ← hs, ← WithTop.LinearOrderedAddCommGroup.coe_sub, scalar_coe, WithTop.coe_le_coe]
  have hd : (∑ v, a v*d v) ≤ (s-r)/t := (le_div_iff₀ ht).mpr (by nlinarith)
  simpa only [one_div_mul_eq_div] using hd

theorem derivative_nonneg_iff_ray (g : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex g) (p d : V → ℝ) (hp : g p ≠ ⊤) :
    0 ≤ DirDeriv g p d ↔
      ∀ t : ℝ, 0 ≤ t → g p ≤ g (fun v => p v+t*d v) := by
  have hne : {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
      L = PosScalarMul (1 / t) (g (fun v => p v+t*d v)-g p)}.Nonempty :=
    ⟨_, 1, by norm_num, rfl⟩
  constructor
  · intro h t ht
    rcases eq_or_lt_of_le ht with rfl | ht
    · simp
    apply (quotient_nonneg_iff _ _ hp t ht).mp
    exact h.trans (csInf_le (quotient_bddBelow g hpoly p d hp) ⟨t, ht, rfl⟩)
  · intro h
    apply le_csInf hne
    rintro L ⟨t, ht, rfl⟩
    exact (quotient_nonneg_iff _ _ hp t ht).mpr (h t ht.le)

end PolyhedralDirectional


open DiscreteConvex.MConvexFunctionsD
open scoped BigOperators

namespace MPolyhedralGlobal
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem closed_sublevel (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (c : ℝ) : IsClosed {z | f z ≤ (c : WithTop ℝ)} := by
  obtain ⟨m, a, b, hab⟩ := hpoly
  have hset : {z | f z ≤ (c : WithTop ℝ)} =
      ⋂ i : Fin m, {z | a i none * c + ∑ v, a i (some v) * z v ≤ b i} := by
    ext z
    have h := Set.ext_iff.mp hab (PolyhedralSupport.epiPoint z c)
    simpa [PolyhedralSupport.epiPoint, Fintype.sum_option] using h
  rw [hset]
  apply isClosed_iInter
  intro i
  apply isClosed_le
  · fun_prop
  · fun_prop

theorem global_min_of_exchange_rays (f : (V → ℝ) → WithTop ℝ)
    (hclosed : ∀ c : ℝ, IsClosed {z | f z ≤ (c : WithTop ℝ)}) (hf : MExchangeAxiomR f)
    (x : V → ℝ) (hx : f x ≠ ⊤)
    (hray : ∀ u v : V, ∀ t : ℝ, 0 ≤ t →
      f x ≤ f (fun w => x w + t * (CharVec v w - CharVec u w : ℝ))) :
    ∀ y, f x ≤ f y := by
  classical
  intro y
  by_contra hnot
  have hfy : f y < f x := lt_of_not_ge hnot
  have hy : f y ≠ ⊤ := ne_top_of_lt hfy
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hy
  let lo : V → ℝ := fun v => min (x v) (y v)
  let hi : V → ℝ := fun v => max (x v) (y v)
  let S := Set.Icc lo hi ∩ {z : V → ℝ | f z ≤ (c : WithTop ℝ)}
  have hSne : S.Nonempty := by
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · intro v; exact min_le_right _ _
    · intro v; exact le_max_right _ _
    · exact hc.symm.le
  have hSc : IsCompact S := isCompact_Icc.inter_right (hclosed c)
  have hcont : Continuous (fun z : V → ℝ => ∑ v, |z v - x v|) := by fun_prop
  obtain ⟨z, hz, hmin⟩ := hSc.exists_isMinOn hSne hcont.continuousOn
  have hzlow : f z ≤ f y := by simpa only [Set.mem_setOf_eq, hc] using hz.2
  have hzdom : f z ≠ ⊤ := ne_top_of_le_ne_top hy hzlow
  have hzne : z ≠ x := by
    intro heq
    rw [heq] at hzlow
    exact (not_le_of_gt hfy) hzlow
  have hex : ∃ u : V, x u < z u := by
    by_contra h
    push_neg at h
    have hcoord : ∃ u : V, z u < x u := by
      by_contra hh
      push_neg at hh
      apply hzne
      funext u
      exact le_antisymm (h u) (hh u)
    obtain ⟨u, hu⟩ := hcoord
    obtain ⟨v, hv, _⟩ := hf x hx z hzdom u hu
    exact (not_lt_of_ge (h v)) hv
  obtain ⟨u, hu⟩ := hex
  obtain ⟨v, hv, a0, ha0, hexc⟩ := hf z hzdom x hx u hu
  change z v < x v at hv
  have huv : u ≠ v := by intro heq; subst v; linarith
  let t : ℝ := min a0 (min (z u - x u) (x v - z v)) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t ≤ a0 := by dsimp [t]; linarith [min_le_left a0 (min (z u-x u) (x v-z v))]
  have htu : t ≤ z u - x u := by
    have hh := (min_le_right a0 (min (z u-x u) (x v-z v))).trans (min_le_left _ _)
    dsimp [t]; linarith
  have htv : t ≤ x v - z v := by
    have hh := (min_le_right a0 (min (z u-x u) (x v-z v))).trans (min_le_right _ _)
    dsimp [t]; linarith
  let z' : V → ℝ := fun w => z w - t * (CharVec u w - CharVec v w : ℝ)
  let x' : V → ℝ := fun w => x w + t * (CharVec u w - CharVec v w : ℝ)
  have hxray : f x ≤ f x' := hray v u t ht.le
  have hznew : f z' ≤ f z := by
    have hh : f z' + f x ≤ f z + f x :=
      (add_le_add_right hxray (f z')).trans (hexc t ht.le hta)
    exact (add_le_add_iff_left_of_ne_top hx).mp hh
  have hz'box : z' ∈ Set.Icc lo hi := by
    constructor <;> intro w
    · by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, Int.cast_one, Int.cast_zero, sub_zero, mul_one]
        exact (min_le_left _ _).trans (by linarith)
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), Int.cast_one, Int.cast_zero, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
          exact (hz.1.1 v).trans (by linarith)
        · simpa [z', CharVec, hwu, hwv] using hz.1.1 w
    · by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, Int.cast_one, Int.cast_zero, sub_zero, mul_one]
        exact (show z u - t ≤ z u by linarith).trans (hz.1.2 u)
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), Int.cast_one, Int.cast_zero, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
          exact (show z v + t ≤ x v by linarith).trans (le_max_left _ _)
        · simpa [z', CharVec, hwu, hwv] using hz.1.2 w
  have hz'S : z' ∈ S := ⟨hz'box, hznew.trans hz.2⟩
  have hdiff : (∑ w, |z' w - x w|) = (∑ w, |z w - x w|) - 2*t := by
    have hpoint (w : V) : |z' w - x w| = |z w - x w| -
        (if w = u then t else 0) - (if w = v then t else 0) := by
      by_cases hwu : w = u
      · subst w
        simp only [z', CharVec, eq_self, if_true, if_neg huv, Int.cast_one, Int.cast_zero, sub_zero, mul_one]
        rw [abs_of_nonneg (by linarith : 0 ≤ z u - t - x u), abs_of_pos (sub_pos.mpr hu)]
        ring
      · by_cases hwv : w = v
        · subst w
          simp only [z', CharVec, eq_self, if_true, if_neg (Ne.symm huv), Int.cast_one, Int.cast_zero, zero_sub, mul_neg, mul_one, sub_neg_eq_add, sub_zero]
          rw [abs_of_nonpos (by linarith : z v + t - x v ≤ 0), abs_of_neg (sub_neg.mpr hv)]
          ring
        · simp [z', CharVec, hwu, hwv]
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp
    ring
  have hbad : (∑ w, |z w - x w|) ≤ (∑ w, |z' w - x w|) := hmin hz'S
  rw [hdiff] at hbad
  linarith

#print axioms global_min_of_exchange_rays
end MPolyhedralGlobal


open DiscreteConvex.MConvexFunctionsD
open scoped BigOperators

namespace MPolyhedralLift
variable {V : Type*} [Fintype V] [DecidableEq V]

def liftPoint (x : V → ℝ) : Option V → ℝ
  | none => -∑ v, x v
  | some v => x v

@[simp] theorem lift_value (f : (V → ℝ) → WithTop ℝ) (x : V → ℝ) :
    LiftedFunctionR f (liftPoint x) = f x := by simp [LiftedFunctionR, liftPoint]

theorem closed_lift_sublevel (f : (V → ℝ) → WithTop ℝ)
    (hc : ∀ c : ℝ, IsClosed {z | f z ≤ (c : WithTop ℝ)}) (c : ℝ) :
    IsClosed {z | LiftedFunctionR f z ≤ (c : WithTop ℝ)} := by
  classical
  have hset : {z | LiftedFunctionR f z ≤ (c : WithTop ℝ)} =
    {z : Option V → ℝ | z none = -∑ v, z (some v)} ∩
      (fun z : Option V → ℝ => fun v => z (some v)) ⁻¹' {z | f z ≤ (c : WithTop ℝ)} := by
    ext z
    simp only [LiftedFunctionR, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    split_ifs <;> simp_all
  rw [hset]
  apply IsClosed.inter
  · apply isClosed_eq <;> fun_prop
  · apply (hc c).preimage
    fun_prop

theorem global_min_of_natural_rays (f : (V → ℝ) → WithTop ℝ)
    (hpoly : IsPolyhedralConvex f) (hf : MNaturalConvexR f)
    (x : V → ℝ) (hx : f x ≠ ⊤)
    (hray : ∀ u v : V, ∀ t : ℝ, 0 ≤ t →
      f x ≤ f (fun w => x w + t * (CharVec v w - CharVec u w : ℝ)))
    (hpos : ∀ v : V, ∀ t : ℝ, 0 ≤ t →
      f x ≤ f (fun w => x w + t * (CharVec v w : ℝ)))
    (hneg : ∀ v : V, ∀ t : ℝ, 0 ≤ t →
      f x ≤ f (fun w => x w + t * (-(CharVec v w : ℝ)))) :
    ∀ y, f x ≤ f y := by
  classical
  have hR : ∀ u v : Option V, ∀ t : ℝ, 0 ≤ t →
      LiftedFunctionR f (liftPoint x) ≤ LiftedFunctionR f
        (fun w => liftPoint x w + t * (CharVec v w - CharVec u w : ℝ)) := by
    intro u v t ht
    rw [lift_value]
    unfold LiftedFunctionR
    split_ifs
    · cases u with
      | none =>
        cases v with
        | none => simp [liftPoint]
        | some v => simpa [liftPoint, CharVec] using hpos v t ht
      | some u =>
        cases v with
        | none => simpa [liftPoint, CharVec] using hneg u t ht
        | some v => simpa [liftPoint, CharVec] using hray u v t ht
    · exact le_top
  have hG := MPolyhedralGlobal.global_min_of_exchange_rays (LiftedFunctionR f)
    (closed_lift_sublevel f (MPolyhedralGlobal.closed_sublevel f hpoly)) hf
    (liftPoint x) (by simpa using hx) hR
  intro y
  simpa using hG (liftPoint y)

end MPolyhedralLift

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℝ) → WithTop ℝ) (hpoly : IsPolyhedralConvex f)
    (x : V → ℝ) (hx : x ∈ DomR f) :
    (MExchangeAxiomR f →
      ((∀ y, f x ≤ f y) ↔ ∀ u v : V, DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) ≥ 0)) ∧
    (MNaturalConvexR f →
      ((∀ y, f x ≤ f y) ↔
        (∀ u v : V, DirDeriv f x (fun w => (CharVec v w - CharVec u w : ℝ)) ≥ 0) ∧
        (∀ v : V, DirDeriv f x (fun w => (CharVec v w : ℝ)) ≥ 0 ∧
          DirDeriv f x (fun w => (-(CharVec v w : ℝ))) ≥ 0))) := by
  have hh (d : V → ℝ) := PolyhedralDirectional.derivative_nonneg_iff_ray f hpoly x d hx
  constructor
  · intro hf
    constructor
    · intro h u v
      exact (hh _).mpr (fun t _ => h _)
    · intro h
      apply MPolyhedralGlobal.global_min_of_exchange_rays f
        (MPolyhedralGlobal.closed_sublevel f hpoly) hf x hx
      intro u v
      exact (hh _).mp (h u v)
  · intro hf
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · intro u v; exact (hh _).mpr (fun t _ => h _)
      · intro v
        exact ⟨(hh _).mpr (fun t _ => h _), (hh _).mpr (fun t _ => h _)⟩
    · rintro ⟨he, hp⟩
      apply MPolyhedralLift.global_min_of_natural_rays f hpoly hf x hx
      · intro u v; exact (hh _).mp (he u v)
      · intro v; exact (hh _).mp (hp v).1
      · intro v; exact (hh _).mp (hp v).2

#print axioms solution
