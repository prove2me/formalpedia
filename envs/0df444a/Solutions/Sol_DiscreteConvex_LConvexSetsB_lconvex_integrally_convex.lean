-- Prove2me | solution 1 for DiscreteConvex.LConvexSetsB.lconvex_integrally_convex
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T07:30:02.160991+00:00
-- url     : https://prove2.me/submissions/7fe04666-7f39-45d4-94ff-ef3eb1ee1c50

import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Definitions.Def_DiscreteConvex_LConvexSetsB_NeighborVec
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntegralNeighborhood
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_DiscreteConvex_LConvexSetsB_IsIntegrallyConvex
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracSortedValues
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracVec
import Definitions.Def_DiscreteConvex_LConvexSetsB_FracLevelSet

set_option autoImplicit false

section
open DiscreteConvex.LConvexSetsB
namespace LConvexSetSeparation
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem shift_mem (D : Set (V → ℤ)) (hD : LConvexSet D) (p : V → ℤ)
    (hp : p ∈ D) (k : ℤ) : (fun v => p v+k) ∈ D := by
  have hper : Function.Periodic (fun p : V → ℤ => p ∈ D) 1 := by
    intro q
    apply propext
    constructor
    · intro hq
      simpa only [Pi.add_apply,Pi.one_apply,add_sub_cancel_right] using (hD.2.2 (q+1) hq).2
    · intro hq
      exact (hD.2.2 q hq).1
  have hh := (hper.zsmul k p).mpr hp
  convert hh using 1
  funext v
  simp

theorem mem_of_pairwise_differences (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℤ)
    (hpair : ∀ u v : V, ∃ q ∈ D, p v-p u ≤ q v-q u) : p ∈ D := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI := h
    obtain ⟨q,hq⟩ := hD.1
    have he : p=q := Subsingleton.elim _ _
    exact he ▸ hq
  | inr h =>
    letI := h
    have hn : (Finset.univ : Finset V).Nonempty := Finset.univ_nonempty
    have hrow (u : V) : ∃ z ∈ D, p ≤ z ∧ z u=p u := by
      choose r hrD hr using hpair u
      let w : V → V → ℤ := fun v a => r v a+(p u-r v u)
      have hwD (v : V) : w v ∈ D := shift_mem D hD (r v) (hrD v) (p u-r v u)
      let z : V → ℤ := Finset.univ.sup' hn w
      refine ⟨z,?_,?_,?_⟩
      · exact Finset.sup'_mem D (fun x hx y hy => (hD.2.1 x hx y hy).1)
          Finset.univ hn w (fun v _ => hwD v)
      · intro v
        have hh := (Finset.le_sup' w (Finset.mem_univ v)) v
        have hv := hr v
        change p v ≤ z v
        change w v v ≤ z v at hh
        dsimp [w] at hh
        omega
      · change (Finset.univ.sup' hn w) u=p u
        rw [Finset.sup'_apply]
        exact Finset.sup'_eq_of_forall hn (fun v => w v u)
          (fun v _ => by dsimp [w]; omega)
    choose r hrD hrLe hrEq using hrow
    let z : V → ℤ := Finset.univ.inf' hn r
    have hzD : z ∈ D := Finset.inf'_mem D (fun x hx y hy => (hD.2.1 x hx y hy).2)
      Finset.univ hn r (fun v _ => hrD v)
    have he : z=p := by
      apply le_antisymm
      · intro v
        have hh := (Finset.inf'_le r (Finset.mem_univ v)) v
        simpa only [hrEq v] using hh
      · exact Finset.le_inf' hn r (fun v _ => hrLe v)
    exact he ▸ hzD

theorem separating_difference (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℤ) (hp : p ∉ D) :
    ∃ u v : V, ∀ q ∈ D, q v-q u ≤ p v-p u-1 := by
  classical
  by_contra h
  push_neg at h
  apply hp
  apply mem_of_pairwise_differences D hD p
  intro u v
  obtain ⟨q,hq,hh⟩ := h u v
  exact ⟨q,hq,by omega⟩

theorem floor_shift_mem (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℝ) (hp : p ∈ convexHull ℝ (IntEmbed D)) (t : ℝ) :
    (fun v => ⌊p v+t⌋) ∈ D := by
  classical
  let N : V → ℤ := fun v => ⌊p v+t⌋
  by_contra hn
  obtain ⟨u,v,hsep⟩ := separating_difference D hD N hn
  let B : ℤ := N v-N u-1
  have hc : Convex ℝ {x : V → ℝ | x v-x u ≤ (B : ℝ)} := by
    intro x hx y hy a b ha hb hab
    change a*x v+b*y v-(a*x u+b*y u) ≤ (B : ℝ)
    change x v-x u ≤ (B : ℝ) at hx
    change y v-y u ≤ (B : ℝ) at hy
    have hx' := mul_le_mul_of_nonneg_left hx ha
    have hy' := mul_le_mul_of_nonneg_left hy hb
    have hB : (a+b)*(B : ℝ)=(B : ℝ) := by rw [hab,one_mul]
    nlinarith
  have hi : IntEmbed D ⊆ {x : V → ℝ | x v-x u ≤ (B : ℝ)} := by
    rintro x ⟨q,hq,rfl⟩
    change (q v : ℝ)-(q u : ℝ) ≤ ((N v-N u-1 : ℤ) : ℝ)
    exact_mod_cast hsep q hq
  have hbound := convexHull_min hi hc hp
  change p v-p u ≤ (B : ℝ) at hbound
  dsimp [B,N] at hbound
  simp only [Int.cast_sub,Int.cast_one] at hbound
  have h1 := Int.floor_le (p v+t)
  have h2 := Int.lt_floor_add_one (p u+t)
  linarith

end LConvexSetSeparation
#print axioms LConvexSetSeparation.mem_of_pairwise_differences
#print axioms LConvexSetSeparation.separating_difference
#print axioms LConvexSetSeparation.floor_shift_mem
end

section
open DiscreteConvex.LConvexSetsB
namespace LIntegralNeighbors
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma frac_nonneg (p : V → ℝ) (v : V) : 0 ≤ FracVec p v := sub_nonneg.mpr (Int.floor_le _)
lemma frac_lt_one (p : V → ℝ) (v : V) : FracVec p v < 1 := Int.fract_lt_one _

lemma sorted_mem_bounds (p : V → ℝ) {a : ℝ} (ha : a ∈ FracSortedValues p) : 0<a ∧ a<1 := by
  classical
  simp only [FracSortedValues,Finset.mem_sort,Finset.mem_filter,Finset.mem_image,
    Finset.mem_univ,true_and] at ha
  obtain ⟨⟨v,hv⟩,hne⟩ := ha
  have hlo := frac_nonneg p v
  have hhi := frac_lt_one p v
  rw [hv] at hlo hhi
  exact ⟨lt_of_le_of_ne hlo (Ne.symm hne),hhi⟩

lemma neighbor_zero (p : V → ℝ) : NeighborVec p 0 = fun v => ⌊p v⌋ := by
  classical
  funext v
  simp [NeighborVec,FracLevelSet]

theorem neighbor_is_shift (p : V → ℝ) (i : ℕ) (hi : i ≤ (FracSortedValues p).length) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ NeighborVec p i = (fun v => ⌊p v+t⌋) := by
  classical
  by_cases hi0 : i=0
  · subst i
    exact ⟨0,le_rfl,by norm_num,by simpa only [add_zero] using neighbor_zero p⟩
  have hidx : i-1 < (FracSortedValues p).length := by omega
  let a := (FracSortedValues p).getD (i-1) 0
  have hamem : a ∈ FracSortedValues p := by
    dsimp [a]
    rw [← List.getElem_eq_getD (h := hidx) 0]
    exact List.getElem_mem hidx
  obtain ⟨ha0,ha1⟩ := sorted_mem_bounds p hamem
  refine ⟨1-a,by linarith,by linarith,?_⟩
  funext v
  have hmem : v ∈ FracLevelSet p i ↔ a ≤ FracVec p v := by simp [FracLevelSet,hi0,a]
  have hp := Int.floor_le (p v)
  have hp' := Int.lt_floor_add_one (p v)
  by_cases h : a ≤ FracVec p v
  · simp only [NeighborVec,if_pos (hmem.mpr h)]
    symm
    apply Int.floor_eq_iff.mpr
    change a ≤ p v-(⌊p v⌋ : ℝ) at h
    push_cast
    constructor <;> linarith
  · simp only [NeighborVec,if_neg (fun hm => h (hmem.mp hm)),add_zero]
    symm
    apply Int.floor_eq_iff.mpr
    change ¬a ≤ p v-(⌊p v⌋ : ℝ) at h
    constructor <;> linarith

theorem neighbor_mem_neighborhood (p : V → ℝ) (i : ℕ)
    (hi : i ≤ (FracSortedValues p).length) : NeighborVec p i ∈ IntegralNeighborhood p := by
  obtain ⟨t,ht0,ht1,he⟩ := neighbor_is_shift p i hi
  rw [he]
  intro v
  constructor
  · exact Int.floor_mono (by linarith)
  · apply Int.floor_le_iff.mpr
    have hh := Int.le_ceil (p v)
    linarith

lemma threshold_is_neighbor (p : V → ℝ) (v : V) (hv : 0 < FracVec p v) :
    ∃ i : ℕ, i ≤ (FracSortedValues p).length ∧
      NeighborVec p i = (fun w => ⌊p w⌋ + if FracVec p v ≤ FracVec p w then 1 else 0) := by
  classical
  have hm : FracVec p v ∈ FracSortedValues p := by
    simp only [FracSortedValues,Finset.mem_sort,Finset.mem_filter,Finset.mem_image,
      Finset.mem_univ,true_and]
    exact ⟨⟨v,rfl⟩,ne_of_gt hv⟩
  obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
  have hget : (FracSortedValues p).getD j 0 = FracVec p v := by
    rw [← List.getElem_eq_getD (h := hj) 0]
    exact he
  refine ⟨j+1,by omega,?_⟩
  funext w
  have hj0 : j+1 ≠ 0 := by omega
  have hmem : w ∈ FracLevelSet p (j+1) ↔ FracVec p v ≤ FracVec p w := by
    simp only [FracLevelSet,if_neg hj0,Nat.add_sub_cancel,Finset.mem_filter,
      Finset.mem_univ,true_and,hget]
  simp only [NeighborVec,hmem]

end LIntegralNeighbors
#print axioms LIntegralNeighbors.neighbor_is_shift
#print axioms LIntegralNeighbors.neighbor_mem_neighborhood
#print axioms LIntegralNeighbors.threshold_is_neighbor
end

section
namespace FractionalThresholdHull
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def support (x : V → ℝ) : Finset V := Finset.univ.filter (fun v => 0 < x v)
noncomputable def threshold (x : V → ℝ) (a : ℝ) : V → ℝ := fun v => if a ≤ x v then 1 else 0

/-- A finite fractional vector is a convex combination of zero and its threshold indicators. -/
theorem mem_of_thresholds (C : Set (V → ℝ)) (hC : Convex ℝ C) (hzero : 0 ∈ C)
    (x : V → ℝ) (hx0 : ∀ v, 0 ≤ x v) (hx1 : ∀ v, x v < 1)
    (hx : ∀ v, 0 < x v → threshold x (x v) ∈ C) : x ∈ C := by
  classical
  suffices h : ∀ n : ℕ, ∀ x : V → ℝ, (support x).card=n →
      (∀ v,0≤x v) → (∀ v,x v<1) → (∀ v,0<x v→threshold x (x v)∈C) → x∈C by
    exact h _ x rfl hx0 hx1 hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn hx0 hx1 hx
    by_cases he : support x = ∅
    · have hxzero : x=0 := by
        funext v
        have hn : ¬0<x v := by
          intro hv
          have hm : v∈support x := by simp [support,hv]
          rw [he] at hm
          simpa using hm
        have hv := hx0 v
        change x v=0
        linarith
      simpa only [hxzero] using hzero
    obtain ⟨u,hu,hmin⟩ := Finset.exists_min_image (support x) x
      (Finset.nonempty_iff_ne_empty.mpr he)
    have hu0 : 0 < x u := by simpa [support] using hu
    let a := x u
    have ha0 : 0<a := hu0
    have ha1 : a<1 := hx1 u
    have hd : 0<1-a := by linarith
    let c : V → ℝ := fun v => if 0<x v then 1 else 0
    let b : V → ℝ := fun v => if 0<x v then (x v-a)/(1-a) else 0
    have hc : c ∈ C := by
      have heq : c=threshold x (x u) := by
        funext v
        by_cases hv : 0<x v
        · have hm : a≤x v := hmin v (by simp [support,hv])
          simp [c,threshold,hv,hm,a] at *
        · have hlt : x v<a := by linarith [hx0 v]
          simp [c,threshold,hv,not_le_of_gt hlt,a] at *
      rw [heq]
      exact hx u hu0
    have hb0 (v : V) : 0≤b v := by
      by_cases hv : 0<x v
      · have hm : a≤x v := hmin v (by simp [support,hv])
        simp only [b,if_pos hv]
        exact div_nonneg (sub_nonneg.mpr hm) hd.le
      · simp [b,hv]
    have hb1 (v : V) : b v<1 := by
      by_cases hv : 0<x v
      · simp only [b,if_pos hv]
        apply (div_lt_iff₀ hd).mpr
        have hh := hx1 v
        linarith
      · simp [b,hv]
    have hbpos (v : V) (hv : 0<b v) : 0<x v := by
      by_contra h
      simp [b,h] at hv
    have hthreshold (v : V) (hv : 0<b v) : threshold b (b v) ∈ C := by
      have hvx := hbpos v hv
      have heq : threshold b (b v)=threshold x (x v) := by
        funext w
        by_cases hwx : 0<x w
        · have he : b v≤b w ↔ x v≤x w := by
            simp only [b,if_pos hvx,if_pos hwx,div_le_div_iff_of_pos_right hd,
              sub_le_sub_iff_right]
          simp only [threshold,he]
        · have hw0 : x w=0 := le_antisymm (le_of_not_gt hwx) (hx0 w)
          have hbw : b w=0 := by simp [b,hwx]
          simp [threshold,hbw,not_le_of_gt hv,hw0,not_le_of_gt hvx]
      rw [heq]
      exact hx v hvx
    have hsub : support b ⊆ support x := by
      intro v hv
      have hv' : 0<b v := by simpa [support] using hv
      have hx' := hbpos v hv'
      simpa [support] using hx'
    have huout : u ∉ support b := by
      have hbu : b u=0 := by simp [b,a,hu0]
      simp [support,hbu]
    have hcard : (support b).card<n := by
      rw [← hn]
      apply Finset.card_lt_card
      exact ⟨hsub,fun h => huout (h hu)⟩
    have hbC : b∈C := ih _ hcard b rfl hb0 hb1 hthreshold
    have heq : a • c+(1-a) • b=x := by
      funext v
      by_cases hv : 0<x v
      · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,c,b,if_pos hv,mul_one]
        field_simp
        ring
      · have hxv : x v=0 := le_antisymm (le_of_not_gt hv) (hx0 v)
        simp [c,b,hv,hxv]
    rw [← heq]
    exact hC hc hbC ha0.le hd.le (by ring)

end FractionalThresholdHull
#print axioms FractionalThresholdHull.mem_of_thresholds
end

section
open DiscreteConvex.LConvexSetsB
namespace LIntegralCombination
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_hull_of_neighbors (D : Set (V → ℤ)) (p : V → ℝ)
    (hN : ∀ i ≤ (FracSortedValues p).length, NeighborVec p i ∈ D) :
    p ∈ convexHull ℝ (IntEmbed D) := by
  classical
  let f : V → ℝ := fun v => (⌊p v⌋ : ℝ)
  let C : Set (V → ℝ) := {x | f+x ∈ convexHull ℝ (IntEmbed D)}
  have hC : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have hc := convex_convexHull ℝ (IntEmbed D) hx hy ha hb hab
    have he : a • (f+x)+b • (f+y)=f+(a • x+b • y) := by
      funext v
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      calc
        a*(f v+x v)+b*(f v+y v) = (a+b)*f v+(a*x v+b*y v) := by ring
        _ = f v+(a*x v+b*y v) := by rw [hab]; simp
    change f+(a • x+b • y) ∈ convexHull ℝ (IntEmbed D)
    simpa only [he] using hc
  have hzero : (0 : V → ℝ) ∈ C := by
    change f+0 ∈ convexHull ℝ (IntEmbed D)
    rw [add_zero]
    apply subset_convexHull
    refine ⟨NeighborVec p 0,hN 0 (Nat.zero_le _),?_⟩
    funext v
    rw [LIntegralNeighbors.neighbor_zero]
  have hthreshold (v : V) (hv : 0<FracVec p v) :
      FractionalThresholdHull.threshold (FracVec p) (FracVec p v) ∈ C := by
    obtain ⟨i,hi,he⟩ := LIntegralNeighbors.threshold_is_neighbor p v hv
    apply subset_convexHull
    refine ⟨NeighborVec p i,hN i hi,?_⟩
    funext w
    rw [he]
    change ((⌊p w⌋ + if FracVec p v≤FracVec p w then 1 else 0 : ℤ) : ℝ) = _
    by_cases hw : FracVec p v≤FracVec p w <;>
      simp [f,FractionalThresholdHull.threshold,hw]
  have hc := FractionalThresholdHull.mem_of_thresholds C hC hzero (FracVec p)
    (LIntegralNeighbors.frac_nonneg p) (LIntegralNeighbors.frac_lt_one p) hthreshold
  have he : f+FracVec p=p := by
    funext v
    change (⌊p v⌋ : ℝ)+(p v-(⌊p v⌋ : ℝ))=p v
    ring
  change f+FracVec p ∈ convexHull ℝ (IntEmbed D) at hc
  simpa only [he] using hc

theorem integrally_convex_of_neighbors (D : Set (V → ℤ))
    (h : ∀ p ∈ convexHull ℝ (IntEmbed D),
      ∀ i ≤ (FracSortedValues p).length, NeighborVec p i ∈ D) : IsIntegrallyConvex D := by
  intro p hp
  apply mem_hull_of_neighbors
  intro i hi
  exact ⟨h p hp i hi,LIntegralNeighbors.neighbor_mem_neighborhood p i hi⟩

end LIntegralCombination
#print axioms LIntegralCombination.mem_hull_of_neighbors
#print axioms LIntegralCombination.integrally_convex_of_neighbors
end

section
open DiscreteConvex.LConvexSetsB
namespace LConvexSetNeighbors
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem neighbor_mem (D : Set (V → ℤ)) (hD : LConvexSet D)
    (p : V → ℝ) (hp : p ∈ convexHull ℝ (IntEmbed D))
    (i : ℕ) (hi : i ≤ (FracSortedValues p).length) : NeighborVec p i ∈ D := by
  obtain ⟨t,_,_,he⟩ := LIntegralNeighbors.neighbor_is_shift p i hi
  rw [he]
  exact LConvexSetSeparation.floor_shift_mem D hD p hp t

end LConvexSetNeighbors
#print axioms LConvexSetNeighbors.neighbor_mem
end

open DiscreteConvex.LConvexSetsB

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (D : Set (V → ℤ))
    (hD : LConvexSet D) :
    (convexHull ℝ (IntEmbed D) =
      {p : V → ℝ | ∀ i ≤ (FracSortedValues p).length, NeighborVec p i ∈ D}) ∧
    IsIntegrallyConvex D := by
  constructor
  · ext p
    constructor
    · intro hp i hi
      exact LConvexSetNeighbors.neighbor_mem D hD p hp i hi
    · intro hp
      exact LIntegralCombination.mem_hull_of_neighbors D p hp
  · apply LIntegralCombination.integrally_convex_of_neighbors D
    intro p hp i hi
    exact LConvexSetNeighbors.neighbor_mem D hD p hp i hi

#print axioms solution
