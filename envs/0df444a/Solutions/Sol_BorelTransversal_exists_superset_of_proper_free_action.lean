-- Prove2me | solution 1 for BorelTransversal.exists_superset_of_proper_free_action
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:18:22.086679+00:00
-- url     : https://prove2.me/submissions/242fded0-7a79-426e-9988-158d96e9f396

import Mathlib

open MeasureTheory Metric Filter Topology Pointwise
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_BorelTransversal_exists_superset_of_proper_free_action

open Set

theorem exists_open_injOn {X H : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [Group H] [TopologicalSpace H] [DiscreteTopology H] [MulAction H X] [ProperSMul H X]
    (hfree : ∀ (h : H) (x : X), h • x = x → h = 1) (x : X) :
    ∃ s : Set X, IsOpen s ∧ x ∈ s ∧ Set.InjOn (Quotient.mk (MulAction.orbitRel H X)) s := by
  classical
  have hpd : ProperlyDiscontinuousSMul H X :=
    properlyDiscontinuousSMul_iff_properSMul.mpr inferInstance
  obtain ⟨K, hKc, hxK⟩ := exists_compact_mem_nhds x
  have hfin : Set.Finite {γ : H | ((γ • ·) '' K ∩ K).Nonempty} :=
    hpd.finite_disjoint_inter_image hKc hKc
  have key : ∀ γ : H, γ ≠ 1 → ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, γ • y ∉ W := by
    intro γ hγ
    have hne : γ • x ≠ x := fun h => hγ (hfree γ x h)
    obtain ⟨u, v, hu, hv, hxu, hxv, huv⟩ := t2_separation hne
    refine ⟨v ∩ (γ • ·) ⁻¹' u, hv.inter (hu.preimage (continuous_const_smul γ)), ⟨hxv, hxu⟩, ?_⟩
    rintro y ⟨hyv, hyu⟩ ⟨hγv, _⟩
    exact Set.disjoint_left.mp huv hyu hγv
  choose! W hWo hxW hW using key
  let S : Set H := {γ : H | ((γ • ·) '' K ∩ K).Nonempty ∧ γ ≠ 1}
  have hS : S.Finite := hfin.subset fun γ hγ => hγ.1
  refine ⟨interior K ∩ ⋂ γ ∈ S, W γ,
    isOpen_interior.inter (hS.isOpen_biInter fun γ hγ => hWo γ hγ.2),
    ⟨mem_interior_iff_mem_nhds.mpr hxK, mem_iInter₂.mpr fun γ hγ => hxW γ hγ.2⟩, ?_⟩
  rintro y ⟨hyK, hyW⟩ z ⟨hzK, hzW⟩ hyz
  have hrel : y ∈ MulAction.orbit H z := (MulAction.orbitRel_apply).mp (Quotient.exact hyz)
  obtain ⟨γ, rfl⟩ := hrel
  by_cases hγ : γ = 1
  · subst hγ; simp
  · exfalso
    have hγS : γ ∈ S := by
      exact ⟨⟨γ • z, ⟨z, interior_subset hzK, rfl⟩, interior_subset hyK⟩, hγ⟩
    exact hW γ hγ z (mem_iInter₂.mp hzW γ hγS) (mem_iInter₂.mp hyW γ hγS)

end Sol_BorelTransversal_exists_superset_of_proper_free_action

open Set Sol_BorelTransversal_exists_superset_of_proper_free_action

theorem solution (X H : Type*) [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    [CommGroup H] [TopologicalSpace H] [DiscreteTopology H] [Countable H]
    [MulAction H X] [ProperSMul H X] (hfree : ∀ (h : H) (x : X), h • x = x → h = 1)
    (E : Set X) (hE : MeasurableSet E)
    (hinj : Set.InjOn (Quotient.mk (MulAction.orbitRel H X)) E) :
    ∃ F : Set X, MeasurableSet F ∧ E ⊆ F ∧
      Set.BijOn (Quotient.mk (MulAction.orbitRel H X)) F Set.univ := by
  classical
  let q := Quotient.mk (MulAction.orbitRel H X)
  let OpenInj := {s : Set X // IsOpen s ∧ InjOn q s}
  let : Nonempty OpenInj := ⟨⟨∅, isOpen_empty, injOn_empty q⟩⟩
  obtain ⟨V, hV⟩ := isLindelof_univ.indexed_countable_subcover
    (Subtype.val : OpenInj → Set X) (fun s ↦ s.property.1) (by
      intro x _
      obtain ⟨s, ho, hx, hi⟩ := exists_open_injOn hfree x
      exact mem_iUnion.mpr ⟨⟨s, ho, hi⟩, hx⟩)
  let U : ℕ → Set X := fun
    | 0 => E
    | n + 1 => (V n).val
  have hU (n : ℕ) : MeasurableSet (U n) ∧ InjOn q (U n) := by
    cases n with
    | zero => exact ⟨hE, hinj⟩
    | succ n => exact ⟨(V n).property.1.measurableSet, (V n).property.2⟩
  let Q (n : ℕ) := q '' U n
  have hsat (n : ℕ) : MeasurableSet (q ⁻¹' Q n) := by
    rw [show q ⁻¹' Q n = ⋃ g : H, (g • ·) '' U n from
      MulAction.quotient_preimage_image_eq_union_mul (U n)]
    exact MeasurableSet.iUnion fun g ↦
      (Homeomorph.smul g).measurableEmbedding.measurableSet_image.mpr (hU n).1
  let F := ⋃ n, U n ∩ q ⁻¹' disjointed Q n
  have hF : MeasurableSet F := MeasurableSet.iUnion fun n ↦ (hU n).1.inter (by
    simp only [disjointed_eq_inter_compl, preimage_inter, preimage_iInter, preimage_compl]
    exact (hsat n).inter (MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ (hsat j).compl))
  refine ⟨F, hF, fun x hx ↦ mem_iUnion.mpr ⟨0, hx, ?_⟩, ⟨fun _ _ => mem_univ _, ?_, ?_⟩⟩
  · change q x ∈ disjointed Q 0
    rw [show disjointed Q 0 = Q 0 from disjointed_bot Q]
    exact mem_image_of_mem q hx
  · rintro x hx y hy (hxy : q x = q y)
    obtain ⟨m, hxm, hqx⟩ := mem_iUnion.mp hx
    obtain ⟨n, hyn, hqy⟩ := mem_iUnion.mp hy
    have hmn : m = n := by
      by_contra hne
      exact (Set.disjoint_left.mp (disjoint_disjointed Q hne)) hqx (hxy.symm ▸ hqy)
    subst n
    exact (hU m).2 hxm hyn hxy
  · intro z _
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hV (mem_univ x))
    have hx : q x ∈ ⋃ n, disjointed Q n := by
      rw [iUnion_disjointed]
      exact mem_iUnion.mpr ⟨n + 1, mem_image_of_mem q hn⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    obtain ⟨y, hy, hyx⟩ := disjointed_subset Q m hm
    have hqy : q y ∈ disjointed Q m := hyx.symm ▸ hm
    exact ⟨y, mem_iUnion.mpr ⟨m, hy, hqy⟩, hyx⟩
