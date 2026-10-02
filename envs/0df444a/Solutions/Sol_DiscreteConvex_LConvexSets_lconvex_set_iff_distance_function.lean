-- Prove2me | solution 1 for DiscreteConvex.LConvexSets.lconvex_set_iff_distance_function
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-02T08:05:14.427949+00:00
-- url     : https://prove2.me/submissions/67f79dca-1872-4b5d-920b-d54e873ab802

import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet
import Definitions.Def_DiscreteConvex_LConvexSets_DistanceFunction
import Definitions.Def_DiscreteConvex_LConvexSets_TriangleInequality
import Definitions.Def_DiscreteConvex_LConvexSets_AdmissiblePotentials
import Definitions.Def_DiscreteConvex_LConvexSets_IsIntegerValuedDist
import Theorems.Thm_DiscreteConvex_LConvexSetsB_lconvex_integrally_convex
import Theorems.Thm_DiscreteConvex_LConvexSetsB_induced_gamma_triangle_and_recovery
import Mathlib.Data.Int.ConditionallyCompleteOrder

set_option autoImplicit false

namespace LDistanceCharacterization
open DiscreteConvex.LConvexSets
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma induced_lower (D : Set (V → ℤ)) (p : V → ℤ) (hp : p ∈ D) (u v : V) :
    (((p v-p u : ℤ) : ℝ) : WithTop ℝ) ≤ DiscreteConvex.LConvexSetsB.InducedGamma D u v :=
  le_csSup (OrderTop.bddAbove _) ⟨p,hp,rfl⟩

lemma induced_upper (D : Set (V → ℤ)) (hne : D.Nonempty) (u v : V)
    (b : WithTop ℝ) (hb : ∀ p ∈ D, (((p v-p u : ℤ) : ℝ) : WithTop ℝ) ≤ b) :
    DiscreteConvex.LConvexSetsB.InducedGamma D u v ≤ b := by
  apply csSup_le (hne.image _)
  rintro _ ⟨p,hp,rfl⟩
  exact hb p hp

theorem induced_integer (D : Set (V → ℤ)) (hne : D.Nonempty) :
    IsIntegerValuedDist (DiscreteConvex.LConvexSetsB.InducedGamma D) := by
  classical
  intro u v
  by_cases ht : DiscreteConvex.LConvexSetsB.InducedGamma D u v=⊤
  · exact Or.inl ht
  obtain ⟨r,hr⟩ := WithTop.ne_top_iff_exists.mp ht
  let S : Set ℤ := (fun p : V → ℤ => p v-p u) '' D
  have hS : S.Nonempty := hne.image _
  have hbound : BddAbove S := by
    refine ⟨⌈r⌉,?_⟩
    rintro z ⟨p,hp,rfl⟩
    have hh := induced_lower D p hp u v
    rw [← hr,WithTop.coe_le_coe] at hh
    have hh' : ((p v-p u : ℤ) : ℝ) ≤ (⌈r⌉ : ℝ) := hh.trans (Int.le_ceil r)
    exact_mod_cast hh'
  refine Or.inr ⟨sSup S,le_antisymm ?_ ?_⟩
  · apply induced_upper D hne u v
    intro p hp
    have hh : p v-p u ≤ sSup S := le_csSup hbound ⟨p,hp,rfl⟩
    exact_mod_cast hh
  · obtain ⟨p,hp,he⟩ := Int.csSup_mem hS hbound
    simpa only [he] using induced_lower D p hp u v

theorem induced_diagonal (D : Set (V → ℤ)) (hne : D.Nonempty) :
    DistanceFunction (DiscreteConvex.LConvexSetsB.InducedGamma D) := by
  intro v
  apply le_antisymm
  · apply induced_upper D hne v v
    intro p hp
    simp
  · obtain ⟨p,hp⟩ := hne
    simpa using induced_lower D p hp v v

theorem lattice_saturation (D : Set (V → ℤ))
    (hD : DiscreteConvex.LConvexSetsB.LConvexSet D) (p : V → ℤ)
    (hp : (fun v => (p v : ℝ)) ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed D)) :
    p ∈ D := by
  rw [(DiscreteConvex.LConvexSetsB.lconvex_integrally_convex D hD).1] at hp
  have hh := hp 0 (Nat.zero_le _)
  have he : DiscreteConvex.LConvexSetsB.NeighborVec (fun v => (p v : ℝ)) 0 = p := by
    classical
    funext v
    simp [DiscreteConvex.LConvexSetsB.NeighborVec,DiscreteConvex.LConvexSetsB.FracLevelSet]
  exact he ▸ hh

theorem representation (D : Set (V → ℤ)) (hne : D.Nonempty) (hD : LConvexSet D) :
    D = {p : V → ℤ | (fun v => (p v : ℝ)) ∈
      AdmissiblePotentials (DiscreteConvex.LConvexSetsB.InducedGamma D)} := by
  have hb : DiscreteConvex.LConvexSetsB.LConvexSet D := ⟨hne,hD.1,hD.2⟩
  have he := (DiscreteConvex.LConvexSetsB.induced_gamma_triangle_and_recovery D hne).2 hb
  ext p
  constructor
  · intro hp
    have hh : (fun v => (p v : ℝ)) ∈ convexHull ℝ (DiscreteConvex.LConvexSetsB.IntEmbed D) :=
      subset_convexHull ℝ _ ⟨p,hp,rfl⟩
    rw [he] at hh
    exact hh
  · intro hp
    apply lattice_saturation D hb p
    rw [he]
    exact hp

theorem potential_set_lconvex (γ : V → V → WithTop ℝ) (hInt : IsIntegerValuedDist γ) :
    LConvexSet {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by
  constructor
  · intro p hp q hq
    have hbounds (u v : V) (hne : u ≠ v) (k : ℤ)
        (hk : γ u v=((k : ℝ) : WithTop ℝ)) : p v-p u ≤ k ∧ q v-q u ≤ k := by
      have hh1 := hp u v hne
      have hh2 := hq u v hne
      rw [hk,WithTop.coe_le_coe] at hh1 hh2
      change (p v : ℝ)-(p u : ℝ) ≤ (k : ℝ) at hh1
      change (q v : ℝ)-(q u : ℝ) ≤ (k : ℝ) at hh2
      exact ⟨by exact_mod_cast hh1,by exact_mod_cast hh2⟩
    constructor
    · intro u v hne
      rcases hInt u v with ht | ⟨k,hk⟩
      · rw [ht]; exact le_top
      · have hh := hbounds u v hne k hk
        rw [hk,WithTop.coe_le_coe]
        have hi : (p ⊔ q) v-(p ⊔ q) u ≤ k := by
          simp only [Pi.sup_apply]
          omega
        change ((p ⊔ q) v : ℝ)-((p ⊔ q) u : ℝ) ≤ (k : ℝ)
        exact_mod_cast hi
    · intro u v hne
      rcases hInt u v with ht | ⟨k,hk⟩
      · rw [ht]; exact le_top
      · have hh := hbounds u v hne k hk
        rw [hk,WithTop.coe_le_coe]
        have hi : (p ⊓ q) v-(p ⊓ q) u ≤ k := by
          simp only [Pi.inf_apply]
          omega
        change ((p ⊓ q) v : ℝ)-((p ⊓ q) u : ℝ) ≤ (k : ℝ)
        exact_mod_cast hi
  · intro p hp
    constructor
    · intro u v hne
      simpa only [Int.cast_add,Int.cast_one,add_sub_add_right_eq_sub] using hp u v hne
    · intro u v hne
      simpa only [Int.cast_sub,Int.cast_one,sub_sub_sub_cancel_right] using hp u v hne

theorem characterization (D : Set (V → ℤ)) (hne : D.Nonempty) :
    LConvexSet D ↔ ∃ γ : V → V → WithTop ℝ, DistanceFunction γ ∧ TriangleInequality γ ∧
      IsIntegerValuedDist γ ∧ D = {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by
  constructor
  · intro hD
    refine ⟨DiscreteConvex.LConvexSetsB.InducedGamma D,induced_diagonal D hne,?_,
      induced_integer D hne,representation D hne hD⟩
    exact (DiscreteConvex.LConvexSetsB.induced_gamma_triangle_and_recovery D hne).1
  · rintro ⟨γ,_,_,hi,he⟩
    rw [he]
    exact potential_set_lconvex γ hi

end LDistanceCharacterization
#print axioms LDistanceCharacterization.induced_integer
#print axioms LDistanceCharacterization.characterization

open DiscreteConvex.LConvexSets

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (D : Set (V → ℤ)) (hD : D.Nonempty) :
    LConvexSet D ↔
      ∃ γ : V → V → WithTop ℝ, DistanceFunction γ ∧ TriangleInequality γ ∧
        IsIntegerValuedDist γ ∧
        D = {p : V → ℤ | (fun v => (p v : ℝ)) ∈ AdmissiblePotentials γ} := by
  exact LDistanceCharacterization.characterization D hD

#print axioms solution
