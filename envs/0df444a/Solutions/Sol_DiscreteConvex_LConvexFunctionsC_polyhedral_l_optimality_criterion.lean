-- Prove2me | solution 1 for DiscreteConvex.LConvexFunctionsC.polyhedral_l_optimality_criterion
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T05:16:43.709441+00:00
-- url     : https://prove2.me/submissions/e5f13f96-ed27-4838-90af-e6768f9378cc

import Definitions.Def_DiscreteConvex_LConvexFunctionsC_IsPolyhedralConvex
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DirDeriv
import Mathlib.Tactic.FieldSimp
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_TRFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_LNaturalConvexR
import Mathlib.Data.Finset.Max


open DiscreteConvex.LConvexFunctionsC
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


open DiscreteConvex.LConvexFunctionsC
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

theorem derivative_eq_of_affine_ray (g : (V → ℝ) → WithTop ℝ)
    (p d : V → ℝ) (hp : g p ≠ ⊤) (r : ℝ)
    (hr : ∀ t : ℝ, 0 < t →
      g (fun v => p v+t*d v) = g p + ((t*r : ℝ) : WithTop ℝ)) :
    DirDeriv g p d = (r : WithTop ℝ) := by
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hp
  have hquot (t : ℝ) (ht : 0 < t) :
      PosScalarMul (1/t) (g (fun v => p v+t*d v)-g p) = (r : WithTop ℝ) := by
    rw [hr t ht, ← hc, ← WithTop.coe_add, ← WithTop.LinearOrderedAddCommGroup.coe_sub, scalar_coe]
    congr 1
    field_simp [ne_of_gt ht]
    <;> ring
  unfold DirDeriv
  have hset : {L : WithTop ℝ | ∃ t : ℝ, 0 < t ∧
      L = PosScalarMul (1/t) (g (fun v => p v+t*d v)-g p)} = { (r : WithTop ℝ) } := by
    ext L
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact hquot t ht
    · intro hL
      refine ⟨1, by norm_num, ?_⟩
      exact (Set.mem_singleton_iff.mp hL).trans (hquot 1 (by norm_num)).symm
  rw [hset, csInf_singleton]

#print axioms quotient_bddBelow
#print axioms derivative_nonneg_iff_ray
#print axioms derivative_eq_of_affine_ray
end PolyhedralDirectional


open DiscreteConvex.LConvexFunctionsC
namespace PolyhedralTranslation
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem derivative_ones_eq_slope (g : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) (hp : g p ≠ ⊤) (r : ℝ)
    (hr : ∀ q : V → ℝ, ∀ t : ℝ,
      g (fun v => q v+t) = g q + ((t*r : ℝ) : WithTop ℝ)) :
    DirDeriv g p (fun _ => (1 : ℝ)) = (r : WithTop ℝ) := by
  apply PolyhedralDirectional.derivative_eq_of_affine_ray g p (fun _ => 1) hp r
  intro t _
  simpa only [mul_one] using hr p t

theorem derivative_ones_zero_of_minimum (g : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) (hp : g p ≠ ⊤) (htr : TRFR g)
    (hmin : ∀ q, g p ≤ g q) :
    DirDeriv g p (fun _ => (1 : ℝ)) = 0 := by
  obtain ⟨r, hr⟩ := htr
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hp
  have hpos := hmin (fun v => p v + 1)
  have hneg := hmin (fun v => p v + (-1))
  rw [hr p 1, ← hc, ← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_le_coe] at hpos
  rw [hr p (-1), ← hc, ← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_le_coe] at hneg
  have hr0 : r = 0 := by linarith
  rw [derivative_ones_eq_slope g p hp r hr, hr0]
  rfl

theorem translation_invariant_of_derivative_zero (g : (V → ℝ) → WithTop ℝ)
    (p : V → ℝ) (hp : g p ≠ ⊤) (htr : TRFR g)
    (hzero : DirDeriv g p (fun _ => (1 : ℝ)) = 0) :
    ∀ q : V → ℝ, ∀ t : ℝ, g (fun v => q v+t) = g q := by
  obtain ⟨r, hr⟩ := htr
  have hcast : (r : WithTop ℝ) = 0 :=
    (derivative_ones_eq_slope g p hp r hr).symm.trans hzero
  have hr0 : r = 0 := by exact_mod_cast hcast
  intro q t
  simpa only [hr0, mul_zero, WithTop.coe_zero, add_zero] using hr q t

#print axioms derivative_ones_zero_of_minimum
#print axioms translation_invariant_of_derivative_zero
end PolyhedralTranslation


set_option autoImplicit false

namespace PolyhedralOrderCriterion
open DiscreteConvex.LConvexFunctionsC
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def positiveGap (p q : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => p v < q v)

@[simp] lemma mem_positiveGap (p q : V → ℝ) (v : V) :
    v ∈ positiveGap p q ↔ p v < q v := by
  classical
  simp [positiveGap]

theorem min_on_upper_cone (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ)
    (hp : g p ≠ ⊤) (hs : SBFR g)
    (hshift : ∀ x : V → ℝ, ∀ a : ℝ, g (fun v => x v + a) = g x)
    (hray : ∀ (Y : Finset V) (t : ℝ), 0 ≤ t →
      g p ≤ g (fun v => p v + t * (if v ∈ Y then (1 : ℝ) else 0))) :
    ∀ q : V → ℝ, (∀ v, p v ≤ q v) → g p ≤ g q := by
  classical
  have H : ∀ n : ℕ, ∀ q : V → ℝ, (positiveGap p q).card = n →
      (∀ v, p v ≤ q v) → g p ≤ g q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro q hcard hle
      let S := positiveGap p q
      by_cases hS : S.Nonempty
      · obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image S (fun v => q v-p v) hS
        let t := q u-p u
        have ht : 0 < t := sub_pos.mpr ((mem_positiveGap p q u).mp hu)
        let q' : V → ℝ := fun v => if v ∈ S then q v-t else q v
        have hgap (v : V) (hv : v ∈ S) : p v+t ≤ q v := by
          have hh := hmin v hv
          dsimp [t]
          linarith
        have heq (v : V) (hv : v ∉ S) : q v = p v := by
          apply le_antisymm _ (hle v)
          exact le_of_not_gt (fun h => hv ((mem_positiveGap p q v).mpr h))
        have hle' (v : V) : p v ≤ q' v := by
          by_cases hv : v ∈ S
          · simp only [q',if_pos hv]
            have := hgap v hv
            linarith
          · simpa [q',hv] using hle v
        have hqq (v : V) : q' v ≤ q v := by
          by_cases hv : v ∈ S <;> simp [q',hv,ht.le]
        have hsub : positiveGap p q' ⊆ S := by
          intro v hv
          exact (mem_positiveGap p q v).mpr
            (lt_of_lt_of_le ((mem_positiveGap p q' v).mp hv) (hqq v))
        have hunot : u ∉ positiveGap p q' := by
          simp [positiveGap,q',hu,t]
        have hstrict : positiveGap p q' ⊂ S := by
          apply ssubset_iff_subset_ne.mpr
          refine ⟨hsub,?_⟩
          intro he
          exact hunot (he.symm ▸ hu)
        have hsmall : (positiveGap p q').card < n := by
          have hh := Finset.card_lt_card hstrict
          exact hh.trans_eq hcard
        have hjoin : q ⊔ (fun v => p v+t) = (fun v => q' v+t) := by
          funext v
          change max (q v) (p v+t) = q' v+t
          by_cases hv : v ∈ S
          · rw [max_eq_left (hgap v hv)]
            simp [q',hv]
          · have hh : q v ≤ p v+t := by rw [heq v hv]; linarith
            rw [max_eq_right hh]
            simp [q',hv,heq v hv]
        have hmeet : q ⊓ (fun v => p v+t) =
            (fun v => p v+t*(if v ∈ S then (1 : ℝ) else 0)) := by
          funext v
          change min (q v) (p v+t) = _
          by_cases hv : v ∈ S
          · rw [min_eq_right (hgap v hv)]
            simp [hv]
          · have hh : q v ≤ p v+t := by rw [heq v hv]; linarith
            rw [min_eq_left hh]
            simp [hv,heq v hv]
        have hstep : g q' ≤ g q := by
          have hh := hs q (fun v => p v+t)
          rw [hjoin,hmeet,hshift p t,hshift q' t] at hh
          have hsum := (add_le_add (le_refl (g q')) (hray S t ht.le)).trans hh
          exact (add_le_add_iff_left_of_ne_top hp).mp hsum
        exact (ih _ hsmall q' rfl hle').trans hstep
      · have he : q = p := by
          funext v
          apply le_antisymm _ (hle v)
          exact le_of_not_gt (fun hv => hS ⟨v,(mem_positiveGap p q v).mpr hv⟩)
        rw [he]
  intro q hle
  exact H _ q rfl hle

theorem global_min_of_indicator_rays (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ)
    (hp : g p ≠ ⊤) (hs : SBFR g)
    (hshift : ∀ x : V → ℝ, ∀ a : ℝ, g (fun v => x v+a) = g x)
    (hray : ∀ (Y : Finset V) (t : ℝ), 0 ≤ t →
      g p ≤ g (fun v => p v+t*(if v ∈ Y then (1 : ℝ) else 0))) :
    ∀ q : V → ℝ, g p ≤ g q := by
  classical
  intro q
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    have he : q=p := Subsingleton.elim _ _
    rw [he]
  | inr h =>
    letI := h
    obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image Finset.univ
      (fun v => q v-p v) Finset.univ_nonempty
    let m := q u-p u
    let q' : V → ℝ := fun v => q v-m
    have hle (v : V) : p v ≤ q' v := by
      have hh := hmin v (Finset.mem_univ v)
      dsimp [q',m]
      linarith
    have hh := min_on_upper_cone g p hp hs hshift hray q' hle
    have he : g q'=g q := by
      convert hshift q (-m) using 1 <;> simp [q',sub_eq_add_neg]
    simpa only [he] using hh

def liftPoint (p : V → ℝ) : Option V → ℝ :=
  fun i => match i with | none => 0 | some v => p v

theorem global_min_of_lnatural_rays (g : (V → ℝ) → WithTop ℝ) (p : V → ℝ)
    (hp : g p ≠ ⊤) (hL : LNaturalConvexR g)
    (hpos : ∀ (Y : Finset V) (t : ℝ), 0 ≤ t →
      g p ≤ g (fun v => p v+t*(if v ∈ Y then (1 : ℝ) else 0)))
    (hneg : ∀ (Y : Finset V) (t : ℝ), 0 ≤ t →
      g p ≤ g (fun v => p v+t*(if v ∈ Y then (-1 : ℝ) else 0))) :
    ∀ q : V → ℝ, g p ≤ g q := by
  classical
  have hbase : LiftedFunctionLR g (liftPoint p) = g p := by
    simp [LiftedFunctionLR,liftPoint]
  have hshift (x : Option V → ℝ) (a : ℝ) :
      LiftedFunctionLR g (fun v => x v+a) = LiftedFunctionLR g x := by
    unfold LiftedFunctionLR
    congr 1
    funext v
    ring
  have hray (Y : Finset (Option V)) (t : ℝ) (ht : 0 ≤ t) :
      LiftedFunctionLR g (liftPoint p) ≤
        LiftedFunctionLR g (fun v => liftPoint p v+t*(if v ∈ Y then (1 : ℝ) else 0)) := by
    rw [hbase]
    by_cases hn : none ∈ Y
    · let S := Finset.univ.filter (fun v : V => some v ∉ Y)
      have he : LiftedFunctionLR g
          (fun v => liftPoint p v+t*(if v ∈ Y then (1 : ℝ) else 0)) =
          g (fun v => p v+t*(if v ∈ S then (-1 : ℝ) else 0)) := by
        unfold LiftedFunctionLR
        congr 1
        funext v
        by_cases hv : some v ∈ Y <;> simp [liftPoint,S,hn,hv] <;> ring
      rw [he]
      exact hneg S t ht
    · let S := Finset.univ.filter (fun v : V => some v ∈ Y)
      have he : LiftedFunctionLR g
          (fun v => liftPoint p v+t*(if v ∈ Y then (1 : ℝ) else 0)) =
          g (fun v => p v+t*(if v ∈ S then (1 : ℝ) else 0)) := by
        unfold LiftedFunctionLR
        congr 1
        funext v
        by_cases hv : some v ∈ Y <;> simp [liftPoint,S,hn,hv]
      rw [he]
      exact hpos S t ht
  have hall := global_min_of_indicator_rays (LiftedFunctionLR g) (liftPoint p)
    (by simpa only [hbase] using hp) hL.1 hshift hray
  intro q
  simpa [LiftedFunctionLR,liftPoint] using hall (liftPoint q)

#print axioms global_min_of_indicator_rays
#print axioms global_min_of_lnatural_rays
end PolyhedralOrderCriterion


set_option autoImplicit false

open DiscreteConvex.LConvexFunctionsC

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (g : (V → ℝ) → WithTop ℝ) (hpoly : IsPolyhedralConvex g)
    (p : V → ℝ) (hp : p ∈ DomR g) :
    ((SBFR g ∧ TRFR g) →
      ((∀ q, g p ≤ g q) ↔
        ((∀ Y : Finset V, DirDeriv g p (fun v => if v ∈ Y then (1 : ℝ) else 0) ≥ 0) ∧
          DirDeriv g p (fun _ => (1 : ℝ)) = 0))) ∧
    (LNaturalConvexR g →
      ((∀ q, g p ≤ g q) ↔
        (∀ Y : Finset V, DirDeriv g p (fun v => if v ∈ Y then (1 : ℝ) else 0) ≥ 0 ∧
          DirDeriv g p (fun v => if v ∈ Y then (-1 : ℝ) else 0) ≥ 0))) := by
  classical
  have hpfinite : g p ≠ ⊤ := hp
  constructor
  · intro h
    constructor
    · intro hmin
      refine ⟨?_, PolyhedralTranslation.derivative_ones_zero_of_minimum g p hpfinite h.2 hmin⟩
      intro Y
      apply (PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mpr
      intro t ht
      exact hmin _
    · rintro ⟨hd, hzero⟩
      apply PolyhedralOrderCriterion.global_min_of_indicator_rays g p hpfinite h.1
        (PolyhedralTranslation.translation_invariant_of_derivative_zero g p hpfinite h.2 hzero)
      intro Y t ht
      exact ((PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mp (hd Y)) t ht
  · intro hL
    constructor
    · intro hmin Y
      constructor
      · apply (PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mpr
        intro t ht
        exact hmin _
      · apply (PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mpr
        intro t ht
        exact hmin _
    · intro hd
      apply PolyhedralOrderCriterion.global_min_of_lnatural_rays g p hpfinite hL
      · intro Y t ht
        exact ((PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mp (hd Y).1) t ht
      · intro Y t ht
        exact ((PolyhedralDirectional.derivative_nonneg_iff_ray g hpoly p _ hpfinite).mp (hd Y).2) t ht

#print axioms solution
