-- Prove2me | solution 1 for DiscreteConvex.LConvexSets.discrete_separation_lconvex
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T08:03:02.996153+00:00
-- url     : https://prove2.me/submissions/ffdc1fd2-05a4-4ecb-83ac-d458923f082c

import Definitions.Def_DiscreteConvex_LConvexSetsB_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSetsB_IntEmbed
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.EReal.Operations

set_option autoImplicit false

section
open DiscreteConvex.LConvexSetsB
namespace LSeparationReconstruction
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

end LSeparationReconstruction
#print axioms LSeparationReconstruction.mem_of_pairwise_differences
#print axioms LSeparationReconstruction.separating_difference
#print axioms LSeparationReconstruction.floor_shift_mem
end

section
namespace DifferenceCycle
open Quiver
variable {V : Type*} [Quiver V]

def NegativeSimple (w : ∀ {u v : V}, (u ⟶ v) → ℤ) : Prop :=
  ∃ (v : V) (c : Path v v), c.addWeight w < 0 ∧ c.vertices.dropLast.Nodup

theorem reduce_path (w : ∀ {u v : V}, (u ⟶ v) → ℤ)
    {a b : V} (p : Path a b) : NegativeSimple w ∨
      ∃ q : Path a b, q.vertices.Nodup ∧ q.addWeight w ≤ p.addWeight w := by
  classical
  induction p with
  | nil => exact Or.inr ⟨Path.nil, by simp, le_rfl⟩
  | @cons b c p e ih =>
    rcases ih with hn | ⟨q,hq,hweight⟩
    · exact Or.inl hn
    by_cases hc : c ∈ q.vertices
    · obtain ⟨l,r,he⟩ := q.exists_eq_comp_of_mem_vertices hc
      have hr : r.vertices.Nodup := by
        rw [he,Path.vertices_comp] at hq
        exact hq.of_append_right
      have hcycle : (r.cons e).vertices.dropLast.Nodup := by
        simpa only [Path.vertices_cons,List.concat_eq_append,List.dropLast_append_cons,
          List.dropLast_singleton,List.append_nil] using hr
      by_cases hn : (r.cons e).addWeight w < 0
      · exact Or.inl ⟨c,r.cons e,hn,hcycle⟩
      · right
        refine ⟨l,?_,?_⟩
        · have hsub : l.vertices.Sublist q.vertices := by
            rw [he,Path.vertices_comp]
            have hh := (List.singleton_sublist.mpr r.start_mem_vertices).append_left
              l.vertices.dropLast
            simpa only [l.dropLast_append_end_eq] using hh
          exact hq.sublist hsub
        · rw [he,Path.addWeight_comp] at hweight
          simp only [Path.addWeight_cons] at hn ⊢
          omega
    · right
      refine ⟨q.cons e,?_,?_⟩
      · exact List.Nodup.concat hc hq
      · simp only [Path.addWeight_cons]
        omega

theorem length_mul_lower (w : ∀ {u v : V}, (u ⟶ v) → ℤ) (M : ℤ)
    (hbound : ∀ {u v : V} (e : u ⟶ v), M ≤ w e)
    {a b : V} (p : Path a b) : (p.length : ℤ)*M ≤ p.addWeight w := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Path.length_cons,Nat.cast_add,Nat.cast_one,Path.addWeight_cons]
    have he := hbound e
    nlinarith

theorem exists_potential_of_no_negative_simple [Fintype V]
    (w : ∀ {u v : V}, (u ⟶ v) → ℤ) (M : ℤ) (hM : M ≤ 0)
    (hbound : ∀ {u v : V} (e : u ⟶ v), M ≤ w e)
    (hn : ¬ NegativeSimple w) :
    ∃ p : V → ℤ, ∀ {u v : V} (e : u ⟶ v), p v-p u ≤ w e := by
  classical
  let costs (v : V) : Set ℤ := {z | ∃ (u : V) (q : Path u v), q.addWeight w = z}
  have hne (v : V) : (costs v).Nonempty := ⟨0,v,Path.nil,by simp⟩
  have hbelow (v : V) : BddBelow (costs v) := by
    refine ⟨(Fintype.card V : ℤ)*M,?_⟩
    rintro z ⟨u,q,rfl⟩
    obtain hneg | ⟨r,hr,hw⟩ := reduce_path w q
    · exact False.elim (hn hneg)
    have hl : r.length ≤ Fintype.card V := by
      have hh := hr.length_le_card
      rw [Path.vertices_length] at hh
      omega
    have hl' : (r.length : ℤ) ≤ (Fintype.card V : ℤ) := by exact_mod_cast hl
    exact (mul_le_mul_of_nonpos_right hl' hM).trans ((length_mul_lower w M hbound r).trans hw)
  refine ⟨fun v => sInf (costs v),?_⟩
  intro u v e
  obtain ⟨a,q,hq⟩ := Int.csInf_mem (hne u) (hbelow u)
  have hv : sInf (costs v) ≤ (q.cons e).addWeight w :=
    csInf_le (hbelow v) ⟨a,q.cons e,rfl⟩
  rw [Path.addWeight_cons,hq] at hv
  change sInf (costs v)-sInf (costs u) ≤ w e
  omega

theorem exists_negative_simple_cycle [Fintype V]
    (w : ∀ {u v : V}, (u ⟶ v) → ℤ) (M : ℤ) (hM : M ≤ 0)
    (hbound : ∀ {u v : V} (e : u ⟶ v), M ≤ w e)
    (hno : ¬ ∃ p : V → ℤ, ∀ {u v : V} (e : u ⟶ v), p v-p u ≤ w e) :
    ∃ (v : V) (c : Path v v), c.addWeight w < 0 ∧ c.vertices.dropLast.Nodup := by
  by_contra h
  exact hno (exists_potential_of_no_negative_simple w M hM hbound h)

end DifferenceCycle
#print axioms DifferenceCycle.reduce_path
#print axioms DifferenceCycle.exists_potential_of_no_negative_simple
#print axioms DifferenceCycle.exists_negative_simple_cycle
end

section
open Quiver
namespace LSeparationCycleCounts
variable {V : Type*} [Quiver V] [DecidableEq V]

def sourceCount (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (v : V) : ℕ :=
  p.addWeight (fun {u _} e => if owner e then (if u=v then 1 else 0) else 0)

def targetCount (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (v : V) : ℕ :=
  p.addWeight (fun {_ w} e => if owner e then (if w=v then 1 else 0) else 0)

def allSourceCount {a b : V} (p : Path a b) (v : V) : ℕ :=
  p.addWeight (fun {u _} _ => if u=v then 1 else 0)

def allTargetCount {a b : V} (p : Path a b) (v : V) : ℕ :=
  p.addWeight (fun {_ w} _ => if w=v then 1 else 0)

lemma addWeight_mono (f g : ∀ {u v : V}, (u ⟶ v) → ℕ)
    (h : ∀ {u v : V} (e : u ⟶ v), f e ≤ g e) {a b : V} (p : Path a b) :
    p.addWeight f ≤ p.addWeight g := by
  induction p with
  | nil => simp
  | cons p e ih => simpa only [Path.addWeight_cons] using add_le_add ih (h e)

lemma source_le (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (v : V) : sourceCount owner p v ≤ allSourceCount p v := by
  apply addWeight_mono
  intro u w e
  split_ifs <;> omega

lemma target_le (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (v : V) : targetCount owner p v ≤ allTargetCount p v := by
  apply addWeight_mono
  intro u w e
  split_ifs <;> omega

lemma all_source_eq_count {a b : V} (p : Path a b) (v : V) :
    allSourceCount p v = p.vertices.dropLast.count v := by
  induction p with
  | nil => simp [allSourceCount]
  | @cons b c p e ih =>
    simp only [allSourceCount,Path.addWeight_cons,Path.vertices_cons,List.concat_eq_append,
      List.dropLast_concat]
    rw [← p.dropLast_append_end_eq,List.count_append,List.count_singleton]
    change allSourceCount p v + (if b=v then 1 else 0) = _
    rw [ih]
    by_cases h : b=v <;> simp [h]

lemma all_counts_balance {a b : V} (p : Path a b) (v : V) :
    allSourceCount p v+(if b=v then 1 else 0) =
      allTargetCount p v+(if a=v then 1 else 0) := by
  induction p with
  | nil => simp [allSourceCount,allTargetCount]
  | @cons b c p e ih =>
    simp only [allSourceCount,allTargetCount,Path.addWeight_cons] at *
    omega

def coefficient (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (v : V) : ℤ :=
  (targetCount owner p v : ℤ)-(sourceCount owner p v : ℤ)

theorem coefficient_values (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a : V} (p : Path a a) (hp : p.vertices.dropLast.Nodup) (v : V) :
    coefficient owner p v = -1 ∨ coefficient owner p v = 0 ∨ coefficient owner p v = 1 := by
  have hS : allSourceCount p v ≤ 1 := by
    rw [all_source_eq_count]
    exact List.nodup_iff_count_le_one.mp hp v
  have he := all_counts_balance p v
  have hT : allTargetCount p v ≤ 1 := by omega
  have hs := source_le owner p v
  have ht := target_le owner p v
  dsimp [coefficient]
  omega

end LSeparationCycleCounts
#print axioms LSeparationCycleCounts.coefficient_values
end

section
open Quiver
namespace LSeparationCycleDot
open LSeparationCycleCounts
variable {V : Type*} [Quiver V] [DecidableEq V] [Fintype V]

lemma coefficient_cons (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b c : V} (p : Path a b) (e : b ⟶ c) (v : V) :
    coefficient owner (p.cons e) v = coefficient owner p v+
      (if owner e then (if c=v then 1 else 0)-(if b=v then 1 else 0) else 0) := by
  cases ho : owner e <;>
    by_cases hc : c=v <;> by_cases hb : b=v <;>
    simp [coefficient,sourceCount,targetCount,Path.addWeight_cons,ho,hc,hb] <;> omega

lemma coefficient_dot (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    {a b : V} (p : Path a b) (x : V → ℤ) :
    (∑ v, coefficient owner p v*x v) =
      p.addWeight (fun {u v} e => if owner e then x v-x u else 0) := by
  induction p with
  | nil => simp [coefficient,sourceCount,targetCount]
  | @cons b c p e ih =>
    simp_rw [coefficient_cons,add_mul,Finset.sum_add_distrib]
    rw [ih,Path.addWeight_cons]
    congr 1
    cases ho : owner e
    · simp [ho]
    · simp [ho,sub_mul,Finset.sum_sub_distrib,eq_comm]

lemma path_comparison (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    (w : ∀ {u v : V}, (u ⟶ v) → ℤ) (x y : V → ℤ)
    (hbound : ∀ {u v : V} (e : u ⟶ v), (if owner e then x v-x u else y v-y u) ≤ w e)
    {a b : V} (p : Path a b) :
    (∑ v, coefficient owner p v*(x v-y v))+(y b-y a) ≤ p.addWeight w := by
  rw [coefficient_dot]
  induction p with
  | nil => simp
  | @cons b c p e ih =>
    simp only [Path.addWeight_cons]
    have hb := hbound e
    cases ho : owner e <;> simp only [ho,Bool.false_eq_true,ite_false,ite_true] at * <;> omega

theorem closed_separation (owner : ∀ {u v : V}, (u ⟶ v) → Bool)
    (w : ∀ {u v : V}, (u ⟶ v) → ℤ) (x y : V → ℤ)
    (hbound : ∀ {u v : V} (e : u ⟶ v), (if owner e then x v-x u else y v-y u) ≤ w e)
    {a : V} (p : Path a a) (hneg : p.addWeight w < 0) :
    (∑ v, (-coefficient owner p v)*y v)+1 ≤ ∑ v, (-coefficient owner p v)*x v := by
  have hh := path_comparison owner w x y hbound p
  simp only [sub_self,add_zero] at hh
  simp_rw [mul_sub] at hh
  rw [Finset.sum_sub_distrib] at hh
  have hx : (∑ v, (-coefficient owner p v)*x v) = -(∑ v, coefficient owner p v*x v) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
  have hy : (∑ v, (-coefficient owner p v)*y v) = -(∑ v, coefficient owner p v*y v) := by
    simp only [neg_mul,Finset.sum_neg_distrib]
  rw [hx,hy]
  omega

end LSeparationCycleDot
#print axioms LSeparationCycleDot.coefficient_dot
#print axioms LSeparationCycleDot.closed_separation
end

section
open Quiver
namespace LSeparationCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]

structure BoundEdge (D1 D2 : Set (V → ℤ)) (u v : V) where
  owner : Bool
  cost : ℤ
  bound : ∀ p ∈ (if owner then D1 else D2), p v-p u ≤ cost

lemma coordinate_bound (p : V → ℤ) (v : V) :
    -((∑ u, (p u).natAbs : ℕ) : ℤ) ≤ p v ∧ p v ≤ ((∑ u, (p u).natAbs : ℕ) : ℤ) := by
  have hh : (p v).natAbs ≤ ∑ u, (p u).natAbs :=
    Finset.single_le_sum (fun u (_ : u ∈ Finset.univ) => Nat.zero_le (p u).natAbs) (Finset.mem_univ v)
  have hu := Int.le_natAbs (a := p v)
  have hl := Int.le_natAbs (a := -p v)
  simp only [Int.natAbs_neg] at hl
  omega

theorem integer_separator (D1 D2 : Set (V → ℤ))
    (hD1 : DiscreteConvex.LConvexSets.LConvexSet D1)
    (hD2 : DiscreteConvex.LConvexSets.LConvexSet D2)
    (hne1 : D1.Nonempty) (hne2 : D2.Nonempty) (hdisj : D1 ∩ D2 = ∅) :
    ∃ x : V → ℤ, (∀ v, x v = -1 ∨ x v = 0 ∨ x v = 1) ∧
      ∀ p ∈ D1, ∀ q ∈ D2, (∑ v, x v*q v)+1 ≤ ∑ v, x v*p v := by
  classical
  letI : Quiver V := ⟨BoundEdge D1 D2⟩
  let w : ∀ {u v : V}, (u ⟶ v) → ℤ := fun e => e.cost
  let owner : ∀ {u v : V}, (u ⟶ v) → Bool := fun e => e.owner
  obtain ⟨p0,hp0⟩ := hne1
  obtain ⟨q0,hq0⟩ := hne2
  let N : ℕ := (∑ v, (p0 v).natAbs)+(∑ v, (q0 v).natAbs)
  let M : ℤ := -2*(N : ℤ)
  have hM : M ≤ 0 := by dsimp [M]; omega
  have hbound : ∀ {u v : V} (e : u ⟶ v), M ≤ w e := by
    intro u v e
    cases ho : e.owner
    · have hb := e.bound q0 (by simpa only [ho,Bool.false_eq_true,ite_false] using hq0)
      have hu := coordinate_bound q0 u
      have hv := coordinate_bound q0 v
      dsimp [M,N,w]
      omega
    · have hb := e.bound p0 (by simpa only [ho,ite_true] using hp0)
      have hu := coordinate_bound p0 u
      have hv := coordinate_bound p0 v
      dsimp [M,N,w]
      omega
  have hno : ¬∃ p : V → ℤ, ∀ {u v : V} (e : u ⟶ v), p v-p u ≤ w e := by
    rintro ⟨p,hp⟩
    have hp1 : p ∈ D1 := by
      by_contra hn
      have hb : DiscreteConvex.LConvexSetsB.LConvexSet D1 := ⟨⟨p0,hp0⟩,hD1.1,hD1.2⟩
      obtain ⟨u,v,he⟩ := LSeparationReconstruction.separating_difference D1 hb p hn
      let e : BoundEdge D1 D2 u v := ⟨true,p v-p u-1,he⟩
      have hh := hp e
      change p v-p u ≤ p v-p u-1 at hh
      omega
    have hp2 : p ∈ D2 := by
      by_contra hn
      have hb : DiscreteConvex.LConvexSetsB.LConvexSet D2 := ⟨⟨q0,hq0⟩,hD2.1,hD2.2⟩
      obtain ⟨u,v,he⟩ := LSeparationReconstruction.separating_difference D2 hb p hn
      let e : BoundEdge D1 D2 u v := ⟨false,p v-p u-1,he⟩
      have hh := hp e
      change p v-p u ≤ p v-p u-1 at hh
      omega
    have hh : p ∈ D1 ∩ D2 := ⟨hp1,hp2⟩
    rw [hdisj] at hh
    exact hh
  obtain ⟨v,c,hneg,hsimple⟩ := DifferenceCycle.exists_negative_simple_cycle w M hM hbound hno
  let x : V → ℤ := fun u => -LSeparationCycleCounts.coefficient owner c u
  refine ⟨x,?_,?_⟩
  · intro u
    have hh := LSeparationCycleCounts.coefficient_values owner c hsimple u
    dsimp [x]
    omega
  · intro p hp q hq
    have hb : ∀ {u v : V} (e : u ⟶ v),
        (if owner e then p v-p u else q v-q u) ≤ w e := by
      intro u v e
      cases ho : e.owner
      · have hh := e.bound q (by simpa only [ho,Bool.false_eq_true,ite_false] using hq)
        simpa only [owner,w,ho,Bool.false_eq_true,ite_false] using hh
      · have hh := e.bound p (by simpa only [ho,ite_true] using hp)
        simpa only [owner,w,ho,ite_true] using hh
    exact LSeparationCycleDot.closed_separation owner w p q hb c hneg

end LSeparationCertificate
#print axioms LSeparationCertificate.integer_separator
end

section
namespace LSeparationEReal
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma extrema_of_pairwise (D1 D2 : Set (V → ℤ)) (x : V → ℤ)
    (h : ∀ p ∈ D1, ∀ q ∈ D2, (∑ v, x v*q v)+1 ≤ ∑ v, x v*p v) :
    sSup ((fun p : V → ℤ => ((∑ v, (x v : ℝ)*(p v : ℝ) : ℝ) : EReal)) '' D2)+1 ≤
      sInf ((fun p : V → ℤ => ((∑ v, (x v : ℝ)*(p v : ℝ) : ℝ) : EReal)) '' D1) := by
  apply le_sInf
  rintro _ ⟨p,hp,rfl⟩
  have hs : sSup ((fun q : V → ℤ => ((∑ v, (x v : ℝ)*(q v : ℝ) : ℝ) : EReal)) '' D2) ≤
      (((∑ v, (x v : ℝ)*(p v : ℝ))-1 : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨q,hq,rfl⟩
    apply EReal.coe_le_coe
    have hh : (∑ v, (x v : ℝ)*(q v : ℝ))+1 ≤ ∑ v, (x v : ℝ)*(p v : ℝ) := by
      exact_mod_cast h p hp q hq
    linarith
  calc
    _ ≤ (((∑ v, (x v : ℝ)*(p v : ℝ))-1 : ℝ) : EReal)+1 := add_le_add hs le_rfl
    _ = ((∑ v, (x v : ℝ)*(p v : ℝ) : ℝ) : EReal) := by
      rw [← EReal.coe_one,← EReal.coe_add,sub_add_cancel]

theorem separation (D1 D2 : Set (V → ℤ))
    (hD1 : DiscreteConvex.LConvexSets.LConvexSet D1)
    (hD2 : DiscreteConvex.LConvexSets.LConvexSet D2) (hdisj : D1 ∩ D2 = ∅) :
    ∃ x : V → ℤ, (∀ v, x v = -1 ∨ x v = 0 ∨ x v = 1) ∧
      sSup ((fun p : V → ℤ => ((∑ v, (x v : ℝ)*(p v : ℝ) : ℝ) : EReal)) '' D2)+1 ≤
        sInf ((fun p : V → ℤ => ((∑ v, (x v : ℝ)*(p v : ℝ) : ℝ) : EReal)) '' D1) := by
  classical
  rcases Set.eq_empty_or_nonempty D1 with rfl | hn1
  · refine ⟨0,fun _ => Or.inr (Or.inl rfl),?_⟩
    simp
  rcases Set.eq_empty_or_nonempty D2 with rfl | hn2
  · refine ⟨0,fun _ => Or.inr (Or.inl rfl),?_⟩
    simp
  obtain ⟨x,hx,hh⟩ := LSeparationCertificate.integer_separator D1 D2 hD1 hD2 hn1 hn2 hdisj
  exact ⟨x,hx,extrema_of_pairwise D1 D2 x hh⟩

end LSeparationEReal
#print axioms LSeparationEReal.separation
end

open DiscreteConvex.LConvexSets

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (D1 D2 : Set (V → ℤ)) (hD1 : LConvexSet D1) (hD2 : LConvexSet D2)
    (hdisj : D1 ∩ D2 = ∅) :
    ∃ x : V → ℤ, (∀ v, x v = -1 ∨ x v = 0 ∨ x v = 1) ∧
      sSup ((fun p : V → ℤ => ((∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D2) + 1 ≤
        sInf ((fun p : V → ℤ => ((∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D1) := by
  exact LSeparationEReal.separation D1 D2 hD1 hD2 hdisj

#print axioms solution
