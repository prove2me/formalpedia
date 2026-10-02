-- Prove2me | solution 1 for DiscreteConvex.Algorithms.base_polyhedron_min_max
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T05:56:18.54711+00:00
-- url     : https://prove2.me/submissions/ad403e97-fa69-4866-9571-0de56c99fd39

import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Abel
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_BasePolyhedron
import Definitions.Def_DiscreteConvex_Algorithms_NegSum
import Definitions.Def_DiscreteConvex_Algorithms_IsIntegerValued
import Mathlib.Data.EReal.Operations
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace SteepestGreedy
open Finset
variable {V A : Type*} [DecidableEq V]
variable [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

lemma greedy_on_ground (f : Finset V → A) (hf0 : f ∅ = 0)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) (T : Finset V) :
    ∃ x : V → A,
      (∀ X ⊆ T, ∑ v ∈ X, x v ≤ f X) ∧
      (∑ v ∈ T, x v = f T) ∧
      (∀ v ∈ T, ∃ S : Finset V, S ⊆ T ∧ v ∉ S ∧ x v = f (insert v S) - f S) := by
  induction T using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, ?_, by simp [hf0], by simp⟩
    intro X hX
    have : X = ∅ := Finset.subset_empty.mp hX
    simp [this, hf0]
  | @insert u T hu ih =>
    obtain ⟨y, hy, htotal, hmarg⟩ := ih
    let x : V → A := fun v => if v = u then f (insert u T) - f T else y v
    have hx_u : x u = f (insert u T) - f T := by simp [x]
    have hx_v (v : V) (hv : v ≠ u) : x v = y v := by simp [x, hv]
    have hsum (X : Finset V) (hXu : u ∉ X) : ∑ v ∈ X, x v = ∑ v ∈ X, y v := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hx_v v (by intro e; subst v; exact hXu hv)
    refine ⟨x, ?_, ?_, ?_⟩
    · intro X hX
      by_cases huX : u ∈ X
      · have he : X.erase u ⊆ T := by
          intro v hv
          have h := hX (Finset.mem_of_mem_erase hv)
          simpa [Finset.mem_insert, (Finset.mem_erase.mp hv).1] using h
        have hunion : T ∪ X = insert u T := by
          ext v
          simp only [Finset.mem_union, Finset.mem_insert]
          constructor
          · rintro (h | h)
            · exact Or.inr h
            · exact Finset.mem_insert.mp (hX h)
          · rintro (rfl | h)
            · exact Or.inr huX
            · exact Or.inl h
        have hinter : T ∩ X = X.erase u := by
          ext v
          simp only [Finset.mem_inter, Finset.mem_erase]
          constructor
          · rintro ⟨ht, hx⟩
            exact ⟨by intro e; subst v; exact hu ht, hx⟩
          · rintro ⟨hne, hx⟩
            exact ⟨he (Finset.mem_erase.mpr ⟨hne,hx⟩),hx⟩
        have hd : f (insert u T) - f T ≤ f X - f (X.erase u) := by
          have hh := hf T X
          rw [hunion, hinter] at hh
          have hk := add_le_add hh (le_refl (-f T - f (X.erase u)))
          convert hk using 1 <;> abel
        have hXe : X = insert u (X.erase u) := (Finset.insert_erase huX).symm
        calc
          ∑ v ∈ X, x v = x u + ∑ v ∈ X.erase u, x v := by
            rw [hXe, Finset.sum_insert (Finset.notMem_erase u X)]
            simp
          _ = (f (insert u T) - f T) + ∑ v ∈ X.erase u, y v := by
            rw [hx_u, hsum _ (Finset.notMem_erase u X)]
          _ ≤ (f X - f (X.erase u)) + f (X.erase u) := add_le_add hd (hy _ he)
          _ = f X := sub_add_cancel _ _
      · rw [hsum X huX]
        apply hy X
        intro v hv
        have h := Finset.mem_insert.mp (hX hv)
        exact h.resolve_left (by intro e; subst v; exact huX hv)
    · rw [Finset.sum_insert hu, hx_u, hsum T hu, htotal, sub_add_cancel]
    · intro v hv
      rcases Finset.mem_insert.mp hv with hvu | hv
      · subst v
        exact ⟨T, Finset.subset_insert u T, hu, hx_u⟩
      · obtain ⟨S, hS, hvS, he⟩ := hmarg v hv
        exact ⟨S, hS.trans (Finset.subset_insert u T), hvS,
          (hx_v v (by intro e; subst v; exact hu hv)).trans he⟩

theorem exists_base [Fintype V] (f : Finset V → A) (hf0 : f ∅ = 0)
    (hf : ∀ X Y, f (X ∪ Y) + f (X ∩ Y) ≤ f X + f Y) :
    ∃ x : V → A, (∀ X : Finset V, ∑ v ∈ X, x v ≤ f X) ∧
      (∑ v, x v = f Finset.univ) ∧
      ∀ v, ∃ S : Finset V, v ∉ S ∧ x v = f (insert v S) - f S := by
  obtain ⟨x,hx,ht,hm⟩ := greedy_on_ground f hf0 hf Finset.univ
  refine ⟨x, fun X => hx X (Finset.subset_univ X), ht, ?_⟩
  intro v
  obtain ⟨S,_,hv,he⟩ := hm v (Finset.mem_univ v)
  exact ⟨S,hv,he⟩

end SteepestGreedy
#print axioms SteepestGreedy.greedy_on_ground
#print axioms SteepestGreedy.exists_base

namespace BaseMinMaxEnvelope
variable {V A : Type*} [DecidableEq V] [LinearOrder A]

noncomputable def lower (f : Finset V → A) (S X : Finset V) : A :=
  ((X ∩ S).powerset).inf' ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩ f

noncomputable def upper (f : Finset V → A) (S X : Finset V) : A :=
  (S.powerset.filter (fun Y => X ∩ S ⊆ Y)).inf'
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr le_rfl, Finset.inter_subset_right⟩⟩ f

theorem lower_witness (f : Finset V → A) (S X : Finset V) :
    ∃ Y : Finset V, Y ⊆ X ∩ S ∧ lower f S X = f Y := by
  obtain ⟨Y,hY,he⟩ := Finset.exists_mem_eq_inf'
    (s := (X ∩ S).powerset) ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩ f
  exact ⟨Y,Finset.mem_powerset.mp hY,he⟩

theorem lower_le (f : Finset V → A) (S X Y : Finset V) (hY : Y ⊆ X ∩ S) :
    lower f S X ≤ f Y := Finset.inf'_le f (Finset.mem_powerset.mpr hY)

theorem upper_witness (f : Finset V → A) (S X : Finset V) :
    ∃ Y : Finset V, Y ⊆ S ∧ X ∩ S ⊆ Y ∧ upper f S X = f Y := by
  obtain ⟨Y,hY,he⟩ := Finset.exists_mem_eq_inf'
    (s := S.powerset.filter (fun Y => X ∩ S ⊆ Y))
    ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr le_rfl, Finset.inter_subset_right⟩⟩ f
  exact ⟨Y,Finset.mem_powerset.mp (Finset.mem_filter.mp hY).1,
    (Finset.mem_filter.mp hY).2,he⟩

theorem upper_le (f : Finset V → A) (S X Y : Finset V)
    (hYS : Y ⊆ S) (hXY : X ∩ S ⊆ Y) : upper f S X ≤ f Y :=
  Finset.inf'_le f (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYS,hXY⟩)

theorem lower_antitone (f : Finset V → A) (S : Finset V) : Antitone (lower f S) := by
  intro X Y hXY
  obtain ⟨Z,hZ,he⟩ := lower_witness f S X
  rw [he]
  apply lower_le
  exact hZ.trans (Finset.inter_subset_inter_right hXY)

theorem upper_monotone (f : Finset V → A) (S : Finset V) : Monotone (upper f S) := by
  intro X Y hXY
  obtain ⟨Z,hZS,hZ,he⟩ := upper_witness f S Y
  rw [he]
  exact upper_le f S X Z hZS ((Finset.inter_subset_inter_right hXY).trans hZ)

theorem lower_empty (f : Finset V → A) (S : Finset V) : lower f S ∅ = f ∅ := by
  obtain ⟨Y,hY,he⟩ := lower_witness f S ∅
  have hY0 : Y = ∅ := Finset.subset_empty.mp (by simpa using hY)
  simpa only [hY0] using he

theorem lower_univ_of_minimum [Fintype V] (f : Finset V → A) (S : Finset V)
    (hmin : ∀ X, f S ≤ f X) : lower f S Finset.univ = f S := by
  apply le_antisymm
  · exact lower_le f S Finset.univ S (by simp)
  · obtain ⟨Y,_,he⟩ := lower_witness f S Finset.univ
    rw [he]
    exact hmin Y

theorem upper_univ [Fintype V] (f : Finset V → A) (S : Finset V) :
    upper f S Finset.univ = f S := by
  obtain ⟨Y,hYS,hSY,he⟩ := upper_witness f S Finset.univ
  have hY : Y = S := Finset.Subset.antisymm hYS (by simpa using hSY)
  simpa only [hY] using he

theorem upper_empty_of_minimum (f : Finset V → A) (S : Finset V)
    (hmin : ∀ X, X ⊆ S → f ∅ ≤ f X) : upper f S ∅ = f ∅ := by
  apply le_antisymm
  · exact upper_le f S ∅ ∅ (Finset.empty_subset _) (by simp)
  · obtain ⟨Y,hYS,_,he⟩ := upper_witness f S ∅
    rw [he]
    exact hmin Y hYS

private theorem insert_inter_of_outside (S X : Finset V) (v : V) (hv : v ∉ S) :
    insert v X ∩ S = X ∩ S := by
  ext w
  by_cases h : w = v
  · subst w
    simp [hv]
  · simp [h]

theorem lower_insert_outside (f : Finset V → A) (S X : Finset V)
    (v : V) (hv : v ∉ S) : lower f S (insert v X) = lower f S X := by
  unfold lower
  simp only [insert_inter_of_outside S X v hv]

theorem upper_insert_outside (f : Finset V → A) (S X : Finset V)
    (v : V) (hv : v ∉ S) : upper f S (insert v X) = upper f S X := by
  unfold upper
  simp only [insert_inter_of_outside S X v hv]

variable [AddCommGroup A] [IsOrderedAddMonoid A]

def Submodular (f : Finset V → A) : Prop :=
  ∀ X Y, f (X ∪ Y)+f (X ∩ Y) ≤ f X+f Y

theorem lower_submodular (f : Finset V → A) (hf : Submodular f) (S : Finset V) :
    Submodular (lower f S) := by
  intro X Y
  obtain ⟨P,hP,hPX⟩ := lower_witness f S X
  obtain ⟨Q,hQ,hQY⟩ := lower_witness f S Y
  have hu : P ∪ Q ⊆ (X ∪ Y) ∩ S := by
    intro v hv
    simp only [Finset.mem_union,Finset.mem_inter] at hv ⊢
    have hp := fun (h : v ∈ P) => Finset.mem_inter.mp (hP h)
    have hq := fun (h : v ∈ Q) => Finset.mem_inter.mp (hQ h)
    tauto
  have hi : P ∩ Q ⊆ (X ∩ Y) ∩ S := by
    intro v hv
    obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp (hP hp)).1,(Finset.mem_inter.mp (hQ hq)).1⟩,
      (Finset.mem_inter.mp (hP hp)).2⟩
  rw [hPX,hQY]
  exact (add_le_add (lower_le f S (X∪Y) (P∪Q) hu)
    (lower_le f S (X∩Y) (P∩Q) hi)).trans (hf P Q)

theorem upper_submodular (f : Finset V → A) (hf : Submodular f) (S : Finset V) :
    Submodular (upper f S) := by
  intro X Y
  obtain ⟨P,hPS,hP,hPX⟩ := upper_witness f S X
  obtain ⟨Q,hQS,hQ,hQY⟩ := upper_witness f S Y
  have hu : (X ∪ Y) ∩ S ⊆ P ∪ Q := by
    intro v hv
    obtain ⟨hvXY,hvS⟩ := Finset.mem_inter.mp hv
    rcases Finset.mem_union.mp hvXY with hvX | hvY
    · exact Finset.mem_union_left _ (hP (Finset.mem_inter.mpr ⟨hvX,hvS⟩))
    · exact Finset.mem_union_right _ (hQ (Finset.mem_inter.mpr ⟨hvY,hvS⟩))
  have hi : (X ∩ Y) ∩ S ⊆ P ∩ Q := by
    intro v hv
    obtain ⟨hvXY,hvS⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr
      ⟨hP (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hvXY).1,hvS⟩),
        hQ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hvXY).2,hvS⟩)⟩
  rw [hPX,hQY]
  exact (add_le_add (upper_le f S (X∪Y) (P∪Q) (Finset.union_subset hPS hQS) hu)
    (upper_le f S (X∩Y) (P∩Q) (Finset.inter_subset_left.trans hPS) hi)).trans (hf P Q)

#print axioms lower_submodular
#print axioms upper_submodular
end BaseMinMaxEnvelope

namespace BaseMinMaxConstruction
open BaseMinMaxEnvelope
variable {V A : Type*} [Fintype V] [DecidableEq V]
variable [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A]

theorem exists_optimal_base (f : Finset V → A) (hf0 : f ∅ = 0) (hf : Submodular f) :
    ∃ (S : Finset V) (z : V → A),
      (∀ X, f S ≤ f X) ∧ (∀ X, ∑ v ∈ X, z v ≤ f X) ∧
      (∑ v, z v = f Finset.univ) ∧ (∑ v, min 0 (z v)) = f S := by
  classical
  obtain ⟨S,hS,hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hminimum (X : Finset V) : f S ≤ f X := hmin X (Finset.mem_univ X)
  let T := Finset.univ \ S
  let c : Finset V → A := fun X => f (S ∪ X)-f S
  have hc0 : c ∅ = 0 := by simp [c]
  have hcnonneg (X : Finset V) : 0 ≤ c X := sub_nonneg.mpr (hminimum _)
  have hc : Submodular c := by
    intro X Y
    have hh := hf (S ∪ X) (S ∪ Y)
    have hu : (S ∪ X) ∪ (S ∪ Y) = S ∪ (X ∪ Y) := by
      ext v
      simp only [Finset.mem_union]
      tauto
    have hi : (S ∪ X) ∩ (S ∪ Y) = S ∪ (X ∩ Y) := by
      ext v
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    rw [hu,hi] at hh
    have hh' := sub_le_sub_right hh (f S+f S)
    dsimp [c]
    convert hh' using 1 <;> abel
  obtain ⟨x,hx,htx,hmx⟩ := SteepestGreedy.exists_base (lower f S)
    ((lower_empty f S).trans hf0) (lower_submodular f hf S)
  obtain ⟨y,hy,hty,hmy⟩ := SteepestGreedy.exists_base (upper c T)
    ((upper_empty_of_minimum c T (fun X _ => by rw [hc0]; exact hcnonneg X)).trans hc0)
    (upper_submodular c hc T)
  have hxneg (v : V) : x v ≤ 0 := by
    obtain ⟨X,_,he⟩ := hmx v
    rw [he]
    exact sub_nonpos.mpr (lower_antitone f S (Finset.subset_insert v X))
  have hypos (v : V) : 0 ≤ y v := by
    obtain ⟨X,_,he⟩ := hmy v
    rw [he]
    exact sub_nonneg.mpr (upper_monotone c T (Finset.subset_insert v X))
  have hxzero (v : V) (hv : v ∉ S) : x v = 0 := by
    obtain ⟨X,_,he⟩ := hmx v
    rw [he,lower_insert_outside f S X v hv,sub_self]
  have hyzero (v : V) (hv : v ∈ S) : y v = 0 := by
    obtain ⟨X,_,he⟩ := hmy v
    have hvT : v ∉ T := by simp [T,hv]
    rw [he,upper_insert_outside c T X v hvT,sub_self]
  have hST : S ∪ T = Finset.univ := by ext v; simp [T]
  have htx' : ∑ v, x v = f S := htx.trans (lower_univ_of_minimum f S hminimum)
  have hty' : ∑ v, y v = f Finset.univ-f S := by
    rw [hty,upper_univ]
    simp only [c,hST]
  refine ⟨S,fun v => x v+y v,hminimum,?_,?_,?_⟩
  · intro X
    rw [Finset.sum_add_distrib]
    have hxu : ∑ v ∈ X, x v ≤ f (X∩S) :=
      (hx X).trans (lower_le f S X (X∩S) le_rfl)
    have hyu : ∑ v ∈ X, y v ≤ c (X∩T) :=
      (hy X).trans (upper_le c T X (X∩T) Finset.inter_subset_right le_rfl)
    apply (add_le_add hxu hyu).trans
    have hh := hf S X
    have hinter : S∩X = X∩S := Finset.inter_comm _ _
    have hunion : S ∪ (X∩T) = S∪X := by
      ext v
      simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,T]
      tauto
    rw [hinter] at hh
    dsimp [c]
    rw [hunion]
    have hh' := sub_le_sub_right hh (f S)
    convert hh' using 1 <;> abel
  · rw [Finset.sum_add_distrib,htx',hty']
    abel
  · have he (v : V) : min 0 (x v+y v) = x v := by
      by_cases hv : v ∈ S
      · rw [hyzero v hv,add_zero,min_eq_right (hxneg v)]
      · rw [hxzero v hv,zero_add,min_eq_left (hypos v)]
    simpa only [he] using htx'

#print axioms exists_optimal_base
end BaseMinMaxConstruction

open DiscreteConvex.MConvexSets DiscreteConvex.Algorithms
namespace BaseMinMaxWrapper
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma negSum_le_subset (x : V → ℝ) (X : Finset V) : NegSum x ≤ ∑ v ∈ X, x v := by
  have h : ∑ v, min 0 (x v) ≤ ∑ v, if v ∈ X then x v else 0 := by
    apply Finset.sum_le_sum
    intro v _
    by_cases hv : v ∈ X
    · simpa [hv] using (min_le_right 0 (x v))
    · simpa [hv] using (min_le_left 0 (x v))
  simpa only [NegSum, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter] using h

lemma inf_eq_of_min (ρ : Finset V → WithTop ℝ) (f : Finset V → ℝ)
    (hf : ∀ X, (f X : WithTop ℝ) = ρ X) (S : Finset V)
    (hS : ∀ X, f S ≤ f X) : Finset.univ.inf ρ = (f S : WithTop ℝ) := by
  apply le_antisymm
  · simpa only [hf] using (Finset.inf_le (f := ρ) (Finset.mem_univ S))
  · apply Finset.le_inf
    intro X _
    rw [← hf X]
    exact WithTop.coe_le_coe.mpr (hS X)

theorem min_max {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hfin : ∀ X, ρ X ≠ ⊤) :
    (sSup {v : WithTop ℝ | ∃ x ∈ BasePolyhedron ρ, v = (NegSum x : WithTop ℝ)} =
      Finset.univ.inf ρ) ∧
    (IsIntegerValued ρ →
      ∃ x ∈ BasePolyhedron ρ, (∀ v : V, ∃ n : ℤ, x v = (n : ℝ)) ∧
        (NegSum x : WithTop ℝ) = Finset.univ.inf ρ) := by
  classical
  choose f hf using fun X => WithTop.ne_top_iff_exists.mp (hfin X)
  have hf0 : f ∅ = 0 := by
    have hh := (hf ∅).trans hρ.1
    exact WithTop.coe_inj.mp hh
  have hsub : BaseMinMaxEnvelope.Submodular f := by
    intro X Y
    have hh := hρ.2.2 X Y
    rw [← hf X, ← hf Y, ← hf (X ∪ Y), ← hf (X ∩ Y),
      ← WithTop.coe_add, ← WithTop.coe_add] at hh
    exact WithTop.coe_le_coe.mp hh
  obtain ⟨S,x,hS,hx,ht,hn⟩ := BaseMinMaxConstruction.exists_optimal_base f hf0 hsub
  have hbase : x ∈ BasePolyhedron ρ := by
    refine ⟨?_, ?_⟩
    · intro X
      rw [← hf X]
      exact WithTop.coe_le_coe.mpr (hx X)
    · rw [ht,hf]
  have hinf := inf_eq_of_min ρ f hf S hS
  constructor
  · rw [hinf]
    apply le_antisymm
    · have hne : Set.Nonempty {v : WithTop ℝ | ∃ y ∈ BasePolyhedron ρ,
          v = (NegSum y : WithTop ℝ)} := ⟨(NegSum x : WithTop ℝ),x,hbase,rfl⟩
      apply csSup_le hne
      rintro v ⟨y,hy,rfl⟩
      have hle := (WithTop.coe_le_coe.mpr (negSum_le_subset y S)).trans (hy.1 S)
      simpa only [← hf S] using hle
    · rw [← hn]
      exact le_csSup (OrderTop.bddAbove _) ⟨x,hbase,rfl⟩
  · intro hint
    choose n hncast using fun X => hint X (f X) (hf X).symm
    have hn0 : n ∅ = 0 := by
      have hh : (n ∅ : ℝ) = 0 := (hncast ∅).trans hf0
      exact_mod_cast hh
    have hnsub : BaseMinMaxEnvelope.Submodular n := by
      intro X Y
      have hh := hsub X Y
      rw [← hncast (X ∪ Y), ← hncast (X ∩ Y), ← hncast X, ← hncast Y] at hh
      exact_mod_cast hh
    obtain ⟨T,z,hT,hz,htz,hnz⟩ := BaseMinMaxConstruction.exists_optimal_base n hn0 hnsub
    let zr : V → ℝ := fun v => (z v : ℝ)
    have hzreal (X : Finset V) : ∑ v ∈ X, zr v ≤ f X := by
      rw [← hncast X]
      dsimp [zr]
      exact_mod_cast hz X
    have htotal : ∑ v, zr v = f Finset.univ := by
      rw [← hncast Finset.univ]
      dsimp [zr]
      exact_mod_cast htz
    have hnegative : NegSum zr = f T := by
      rw [← hncast T]
      change (∑ v, min 0 ((z v : ℤ) : ℝ)) = (n T : ℝ)
      exact_mod_cast hnz
    have hTreal (X : Finset V) : f T ≤ f X := by
      rw [← hncast T, ← hncast X]
      exact_mod_cast hT X
    refine ⟨zr, ⟨?_, ?_⟩, fun v => ⟨z v,rfl⟩, ?_⟩
    · intro X
      rw [← hf X]
      exact WithTop.coe_le_coe.mpr (hzreal X)
    · rw [htotal,hf]
    · rw [hnegative,inf_eq_of_min ρ f hf T hTreal]

end BaseMinMaxWrapper
#print axioms BaseMinMaxWrapper.min_max

open DiscreteConvex.MConvexSets DiscreteConvex.Algorithms

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) (hfin : ∀ X, ρ X ≠ ⊤) :
    (sSup {v : WithTop ℝ | ∃ x ∈ BasePolyhedron ρ, v = (NegSum x : WithTop ℝ)} =
      Finset.univ.inf ρ) ∧
    (IsIntegerValued ρ →
      ∃ x ∈ BasePolyhedron ρ, (∀ v : V, ∃ n : ℤ, x v = (n : ℝ)) ∧
        (NegSum x : WithTop ℝ) = Finset.univ.inf ρ) :=
  BaseMinMaxWrapper.min_max ρ hρ hfin

#print axioms solution
