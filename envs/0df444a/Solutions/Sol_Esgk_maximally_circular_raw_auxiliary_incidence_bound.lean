-- Prove2me | solution 1 for Esgk.maximally_circular_raw_auxiliary_incidence_bound
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-16T06:10:55.935125+00:00
-- url     : https://prove2.me/submissions/d7bf49b5-fcc7-4adf-a7cd-3349701f4042

import Theorems.Thm_Esgk_maximallyCircular_twoSamplePairSeparation
import Definitions.Def_Esgk_AffineLinePolynomialRestriction
import Definitions.Def_Esgk_BivariateCornerNormalForm
import Definitions.Def_Esgk_CircularTangentIsotropicFaces
import Definitions.Def_Esgk_ConnectedLocalHomeomorphReal
import Definitions.Def_Esgk_DistanceNewtonPersistentTangentRoots
import Definitions.Def_Esgk_FiniteRealCutIntervals
import Definitions.Def_Esgk_IntrinsicPartitionScale
import Definitions.Def_Esgk_IrreduciblePlaneAffineIsometryDistanceTransport
import Definitions.Def_Esgk_MaximallyCircularDegreeTwoCircle
import Definitions.Def_Esgk_MaximallyCircularIntrinsicCellCover
import Definitions.Def_Esgk_MaximallyCircularIsotropicBidegree
import Definitions.Def_Esgk_MultivariateEliminationResultant
import Definitions.Def_Esgk_PlaneCurveCellVisits
import Definitions.Def_Esgk_PlaneCurveRadiusFibers
import Definitions.Def_Esgk_PlaneCurveSafeSample
import Definitions.Def_Esgk_PlaneIsometryFixedPointBisector
import Definitions.Def_Esgk_PlaneIsotropicCoordinates
import Definitions.Def_Esgk_PlaneProjectiveAffineChart
import Definitions.Def_Esgk_SelfCurveRetainedNonreflection
import Definitions.Def_Esgk_SharpResultantFiniteSetCount
import Definitions.Def_Esgk_TwoPairDistanceQuadricPolynomialPullback
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_Basic
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_PlaneArcSeparation
import Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearExists
import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Order.IntermediateValue
section

open Esgk
open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem Esgk.maximallyCircular_pairSeparation
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G) :
    ∃ Δ : Finset (S × S),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card ∧
      ∀ ij, ij ∉ Δ → ∀ kl, kl ∉ Δ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2) (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2) (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by
  obtain ⟨Δ₁, Δ₂, hcard₁, hcard₂, hfinite₁, hfinite₂⟩ :=
    Esgk.maximallyCircular_twoSamplePairSeparation hGirreducible hmax hnotCircle S S hS hS
  exact ⟨Δ₁, hcard₁, hfinite₁⟩

end
 

 



section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology Filter

namespace Esgk


theorem exists_connectedComponentIn_frontier_of_closure_minimum
    {M : Type*} [TopologicalSpace M] [LocallyConnectedSpace M]
    {U : Set M} (hU : IsOpen U) (f : M → ℝ)
    (hf : IsLocalHomeomorph (fun p : U ↦ f p))
    {x : M}
    (hminimum : ∃ p ∈ closure (connectedComponentIn U x),
      ∀ q ∈ connectedComponentIn U x, f p ≤ f q) :
    ∃ p ∈ closure (connectedComponentIn U x), p ∈ frontier U := by
  obtain ⟨p, hpclosure, hmin⟩ := hminimum
  refine ⟨p, hpclosure, ?_⟩
  rw [frontier, hU.interior_eq]
  refine ⟨closure_mono (connectedComponentIn_subset U x) hpclosure, ?_⟩
  intro hpU
  have hDopen : IsOpen (connectedComponentIn U p) := hU.connectedComponentIn
  have hpD : p ∈ connectedComponentIn U p := mem_connectedComponentIn hpU
  obtain ⟨y, hyD, hyC⟩ := mem_closure_iff.mp hpclosure _ hDopen hpD
  have hCD : connectedComponentIn U x = connectedComponentIn U p :=
    (connectedComponentIn_eq hyC).trans (connectedComponentIn_eq hyD).symm
  have hpC : p ∈ connectedComponentIn U x := by rwa [hCD]
  let V : Set U := {q | (q : M) ∈ connectedComponentIn U x}
  have hV : IsOpen V :=
    (hU.connectedComponentIn (x := x)).preimage continuous_subtype_val
  have himage : (fun q : U ↦ f q) '' V = f '' connectedComponentIn U x := by
    ext r
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, connectedComponentIn_subset U x hq⟩, hq, rfl⟩
  have hopen : IsOpen (f '' connectedComponentIn U x) := by
    rw [← himage]
    exact hf.isOpenMap V hV
  have hfp : f p ∈ f '' connectedComponentIn U x := ⟨p, hpC, rfl⟩
  obtain ⟨r, hrlt, q, hq, hqr⟩ := Filter.Eventually.exists_lt (hopen.mem_nhds hfp)
  have hbound := hmin q hq
  linarith

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology Filter

namespace Esgk

variable {X : Type*} [TopologicalSpace X] [T2Space X] {f : X → ℝ}


@[simp]
theorem homeomorphRangeOfIsLocalHomeomorphReal_apply_coe [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) (x : X) :
    (homeomorphRangeOfIsLocalHomeomorphReal hf x : ℝ) = f x := rfl

omit [T2Space X] in
 

theorem isOpen_ordConnected_range_of_isLocalHomeomorph_real [ConnectedSpace X]
    (hf : IsLocalHomeomorph f) : IsOpen (Set.range f) ∧ Set.OrdConnected (Set.range f) :=
  ⟨hf.isOpenMap.isOpen_range, (isPreconnected_range hf.continuous).ordConnected⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk

variable {M : Type*} [TopologicalSpace M] [T1Space M]

 
private theorem inline_Esgk_FiniteBoundaryCurveComponents__exists_two_preconnected_chart_sides (B : Finset M) {b : M}
    (e : OpenPartialHomeomorph M ℝ) (hb : b ∈ e.source) :
    ∃ L R N : Set M, IsOpen N ∧ b ∈ N ∧ IsPreconnected L ∧ IsPreconnected R ∧
      Disjoint L (B : Set M) ∧ Disjoint R (B : Set M) ∧
      N \ {b} ⊆ L ∪ R := by
  classical
  let A : Set M := (B.erase b : Set M)ᶜ
  have hAopen : IsOpen A := (B.erase b).finite_toSet.isClosed.isOpen_compl
  have hbA : b ∈ A := by simp [A]
  have hcenter : e b ∈ e.target ∩ e.symm ⁻¹' A := by
    refine ⟨e.map_source hb, ?_⟩
    change e.symm (e b) ∈ A
    simpa only [e.left_inv hb] using hbA
  obtain ⟨ε, hε, hsmall⟩ := Metric.mem_nhds_iff.mp
    ((e.isOpen_inter_preimage_symm hAopen).mem_nhds hcenter)
  have havoid : ∀ t ∈ Metric.ball (e b) ε, t ≠ e b → e.symm t ∉ (B : Set M) := by
    intro t ht hne hB
    have hne' : e.symm t ≠ b := by
      intro heq
      apply hne
      rw [← e.right_inv (hsmall ht).1, heq]
    have herase : e.symm t ∈ (B.erase b : Set M) :=
      Finset.mem_erase.mpr ⟨hne', hB⟩
    exact (hsmall ht).2 herase
  let I₀ : Set ℝ := Ioo (e b - ε) (e b)
  let I₁ : Set ℝ := Ioo (e b) (e b + ε)
  have hI₀ : I₀ ⊆ Metric.ball (e b) ε := by
    intro t ht
    rw [Real.ball_eq_Ioo]
    exact ⟨ht.1, ht.2.trans (lt_add_of_pos_right _ hε)⟩
  have hI₁ : I₁ ⊆ Metric.ball (e b) ε := by
    intro t ht
    rw [Real.ball_eq_Ioo]
    exact ⟨(sub_lt_self _ hε).trans ht.1, ht.2⟩
  have hdisjoint {I : Set ℝ} (hI : I ⊆ Metric.ball (e b) ε)
      (hne : ∀ t ∈ I, t ≠ e b) : Disjoint (e.symm '' I) (B : Set M) := by
    apply Set.disjoint_left.mpr
    rintro p ⟨t, ht, rfl⟩ hp
    exact havoid t (hI ht) (hne t ht) hp
  let N : Set M := e.source ∩ e ⁻¹' Metric.ball (e b) ε
  refine ⟨e.symm '' I₀, e.symm '' I₁, N,
    e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hb, Metric.mem_ball_self hε⟩,
    ?_, ?_, hdisjoint hI₀ (fun _ ht ↦ ne_of_lt ht.2),
    hdisjoint hI₁ (fun _ ht ↦ ne_of_gt ht.1), ?_⟩
  · exact isPreconnected_Ioo.image e.symm
      (e.symm.continuousOn.mono (fun t ht ↦ (hsmall (hI₀ ht)).1))
  · exact isPreconnected_Ioo.image e.symm
      (e.symm.continuousOn.mono (fun t ht ↦ (hsmall (hI₁ ht)).1))
  · intro p hp
    have hpsource : p ∈ e.source := hp.1.1
    have hpne : p ≠ b := by simpa only [Set.mem_singleton_iff] using hp.2
    have hene : e p ≠ e b := fun heq ↦ hpne (e.injOn hpsource hb heq)
    have hbounds : e b - ε < e p ∧ e p < e b + ε := by
      simpa only [Set.mem_preimage, Real.ball_eq_Ioo, Set.mem_Ioo] using hp.1.2
    rcases lt_or_gt_of_ne hene with hlt | hgt
    · exact Or.inl ⟨e p, ⟨hbounds.1, hlt⟩, e.left_inv hpsource⟩
    · exact Or.inr ⟨e p, ⟨hgt, hbounds.2⟩, e.left_inv hpsource⟩

omit [T1Space M] in
 
private theorem inline_Esgk_FiniteBoundaryCurveComponents__preconnected_subset_of_disjoint_frontier {U A : Set M}
    (hU : IsOpen U) (hA : IsPreconnected A) (hfrontier : Disjoint A (frontier U))
    (hmeet : (A ∩ U).Nonempty) : A ⊆ U := by
  have hcover : A ⊆ U ∪ interior Uᶜ := by
    intro p hp
    have houtside : p ∈ (frontier U)ᶜ := fun h ↦ Set.disjoint_left.mp hfrontier hp h
    rw [compl_frontier_eq_union_interior] at houtside
    exact houtside.imp (fun h ↦ interior_subset h) id
  have hdisjoint : Disjoint U (interior Uᶜ) := by
    apply Set.disjoint_left.mpr
    intro p hp hi
    exact interior_subset hi hp
  rcases IsPreconnected.subset_or_subset hU isOpen_interior hdisjoint hcover hA with h | h
  · exact h
  · obtain ⟨p, hpA, hpU⟩ := hmeet
    exact False.elim (interior_subset (h hpA) hpU)


omit [T1Space M] in
private theorem inline_Esgk_FiniteBoundaryCurveComponents__connectedComponentIn_eq_chosenSideComponent {U A : Set M}
    (hU : IsOpen U) (hA : IsPreconnected A) (hfrontier : Disjoint A (frontier U))
    {x p : M} (hpC : p ∈ connectedComponentIn U x) (hpA : p ∈ A) :
    connectedComponentIn U x = bundle_Esgk_FiniteBoundaryCurveComponents_chosenSideComponent U A := by
  have hmeet : (A ∩ U).Nonempty := ⟨p, hpA, connectedComponentIn_subset U x hpC⟩
  have hAU : A ⊆ U := inline_Esgk_FiniteBoundaryCurveComponents__preconnected_subset_of_disjoint_frontier hU hA hfrontier hmeet
  have hsubset : A ⊆ connectedComponentIn U p := hA.subset_connectedComponentIn hpA hAU
  rw [bundle_Esgk_FiniteBoundaryCurveComponents_chosenSideComponent, dif_pos hmeet]
  exact (connectedComponentIn_eq hpC).trans
    (connectedComponentIn_eq (hsubset hmeet.choose_spec.1))


theorem connectedComponentIn_finite_and_ncard_le_of_finite_boundary
    (U : Set M) (B : Finset M) (hU : IsOpen U) (hUB : Disjoint U (B : Set M))
    (hfrontier : frontier U ⊆ (B : Set M))
    (hboundary : ∀ x ∈ U, ∃ b ∈ B, b ∈ closure (connectedComponentIn U x))
    (hcharts : ∀ b ∈ B, ∃ e : OpenPartialHomeomorph M ℝ, b ∈ e.source) :
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x}.Finite ∧
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x}.ncard ≤ 2 * B.card := by
  classical
  have hlocal : ∀ b : {p // p ∈ B}, ∃ L R N : Set M,
      IsOpen N ∧ (b : M) ∈ N ∧ IsPreconnected L ∧ IsPreconnected R ∧
        Disjoint L (B : Set M) ∧ Disjoint R (B : Set M) ∧
        N \ {(b : M)} ⊆ L ∪ R := by
    intro b
    obtain ⟨e, he⟩ := hcharts b b.property
    exact inline_Esgk_FiniteBoundaryCurveComponents__exists_two_preconnected_chart_sides B e he
  choose L R N hNopen hbN hL hR hLB hRB hcover using hlocal
  let side : ({p // p ∈ B} × Bool) → Set M :=
    fun v ↦ if v.2 then R v.1 else L v.1
  let W : Finset (Set M) :=
    Finset.univ.image (fun v : {p // p ∈ B} × Bool ↦ bundle_Esgk_FiniteBoundaryCurveComponents_chosenSideComponent U (side v))
  have hWcard : W.card ≤ 2 * B.card := by
    calc
      W.card ≤ (Finset.univ : Finset ({p // p ∈ B} × Bool)).card := Finset.card_image_le
      _ = 2 * B.card := by simp [Nat.mul_comm]
  have hsubset : {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x} ⊆ (W : Set (Set M)) := by
    rintro C ⟨x, hx, rfl⟩
    obtain ⟨b, hb, hbclosure⟩ := hboundary x hx
    let b' : {p // p ∈ B} := ⟨b, hb⟩
    obtain ⟨p, hpN, hpC⟩ := mem_closure_iff.mp hbclosure (N b') (hNopen b') (hbN b')
    have hpne : p ≠ b := by
      intro heq
      have hpB : p ∈ (B : Set M) := by
        change p ∈ B
        simpa only [heq] using hb
      exact Set.disjoint_left.mp hUB (connectedComponentIn_subset U x hpC) hpB
    have hpside : p ∈ L b' ∪ R b' := hcover b' ⟨hpN, hpne⟩
    have hLfrontier : Disjoint (L b') (frontier U) := by
      apply Set.disjoint_left.mpr
      intro q hqL hqF
      exact Set.disjoint_left.mp (hLB b') hqL (hfrontier hqF)
    have hRfrontier : Disjoint (R b') (frontier U) := by
      apply Set.disjoint_left.mpr
      intro q hqR hqF
      exact Set.disjoint_left.mp (hRB b') hqR (hfrontier hqF)
    rcases hpside with hpL | hpR
    · have heq := inline_Esgk_FiniteBoundaryCurveComponents__connectedComponentIn_eq_chosenSideComponent hU (hL b') hLfrontier hpC hpL
      apply Finset.mem_image.mpr
      refine ⟨(b', false), Finset.mem_univ _, ?_⟩
      simpa [side] using heq.symm
    · have heq := inline_Esgk_FiniteBoundaryCurveComponents__connectedComponentIn_eq_chosenSideComponent hU (hR b') hRfrontier hpC hpR
      apply Finset.mem_image.mpr
      refine ⟨(b', true), Finset.mem_univ _, ?_⟩
      simpa [side] using heq.symm
  refine ⟨W.finite_toSet.subset hsubset, ?_⟩
  calc
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x}.ncard ≤
        (W : Set (Set M)).ncard := Set.ncard_le_ncard hsubset W.finite_toSet
    _ = W.card := Set.ncard_coe_finset W
    _ ≤ 2 * B.card := hWcard


theorem connectedComponentIn_closure_finite_and_ncard_le_two_of_not_mem
    (U : Set M) (B : Finset M) (hU : IsOpen U)
    (hfrontier : frontier U ⊆ (B : Set M)) {b : M} (hbU : b ∉ U)
    (e : OpenPartialHomeomorph M ℝ) (hb : b ∈ e.source) :
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.Finite ∧
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.ncard ≤ 2 := by
  classical
  obtain ⟨L, R, N, hNopen, hbN, hL, hR, hLB, hRB, hcover⟩ :=
    inline_Esgk_FiniteBoundaryCurveComponents__exists_two_preconnected_chart_sides B e hb
  let side : Bool → Set M := fun v ↦ if v then R else L
  let W : Finset (Set M) :=
    Finset.univ.image (fun v : Bool ↦ bundle_Esgk_FiniteBoundaryCurveComponents_chosenSideComponent U (side v))
  have hWcard : W.card ≤ 2 := by
    calc
      W.card ≤ (Finset.univ : Finset Bool).card := Finset.card_image_le
      _ = 2 := by simp
  have hLfrontier : Disjoint L (frontier U) := by
    apply Set.disjoint_left.mpr
    intro q hqL hqF
    exact Set.disjoint_left.mp hLB hqL (hfrontier hqF)
  have hRfrontier : Disjoint R (frontier U) := by
    apply Set.disjoint_left.mpr
    intro q hqR hqF
    exact Set.disjoint_left.mp hRB hqR (hfrontier hqF)
  have hsubset :
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C} ⊆
        (W : Set (Set M)) := by
    rintro C ⟨x, hx, rfl, hbclosure⟩
    obtain ⟨p, hpN, hpC⟩ := mem_closure_iff.mp hbclosure N hNopen hbN
    have hpne : p ≠ b := by
      intro heq
      exact hbU (heq ▸ connectedComponentIn_subset U x hpC)
    rcases hcover ⟨hpN, hpne⟩ with hpL | hpR
    · have heq := inline_Esgk_FiniteBoundaryCurveComponents__connectedComponentIn_eq_chosenSideComponent hU hL hLfrontier hpC hpL
      apply Finset.mem_image.mpr
      exact ⟨false, Finset.mem_univ _, by simpa [side] using heq.symm⟩
    · have heq := inline_Esgk_FiniteBoundaryCurveComponents__connectedComponentIn_eq_chosenSideComponent hU hR hRfrontier hpC hpR
      apply Finset.mem_image.mpr
      exact ⟨true, Finset.mem_univ _, by simpa [side] using heq.symm⟩
  refine ⟨W.finite_toSet.subset hsubset, ?_⟩
  calc
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.ncard ≤
        (W : Set (Set M)).ncard := Set.ncard_le_ncard hsubset W.finite_toSet
    _ = W.card := Set.ncard_coe_finset W
    _ ≤ 2 := hWcard

omit [T1Space M] in
 

theorem connectedComponentIn_closure_finite_and_ncard_le_one_of_mem
    [LocallyConnectedSpace M] (U : Set M) (hU : IsOpen U) {b : M} (hbU : b ∈ U) :
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.Finite ∧
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.ncard ≤ 1 := by
  have hsubset :
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C} ⊆
        {connectedComponentIn U b} := by
    rintro C ⟨x, hx, rfl, hbclosure⟩
    obtain ⟨p, hpD, hpC⟩ := mem_closure_iff.mp hbclosure (connectedComponentIn U b)
      hU.connectedComponentIn (mem_connectedComponentIn hbU)
    exact (connectedComponentIn_eq hpC).trans (connectedComponentIn_eq hpD).symm
  refine ⟨(Set.finite_singleton _).subset hsubset, ?_⟩
  simpa only [Set.ncard_singleton] using
    Set.ncard_le_ncard hsubset (Set.finite_singleton _)


theorem connectedComponentIn_closure_finite_and_ncard_le_two
    [LocallyConnectedSpace M] (U : Set M) (B : Finset M) (hU : IsOpen U)
    (hfrontier : frontier U ⊆ (B : Set M)) {b : M}
    (e : OpenPartialHomeomorph M ℝ) (hb : b ∈ e.source) :
    {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.Finite ∧
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ b ∈ closure C}.ncard ≤ 2 := by
  by_cases hbU : b ∈ U
  · obtain ⟨hfinite, hcard⟩ :=
      connectedComponentIn_closure_finite_and_ncard_le_one_of_mem U hU hbU
    exact ⟨hfinite, hcard.trans (by omega)⟩
  · exact connectedComponentIn_closure_finite_and_ncard_le_two_of_not_mem
      U B hU hfrontier hbU e hb

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk


theorem finiteIncidenceCount_eq_card_filter_product {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) :
    finiteIncidenceCount P C R =
      ((P.product C).filter (fun xb : α × β ↦ R xb.1 xb.2)).card := by
  classical
  simp only [finiteIncidenceCount, Finset.card_filter]
  exact (Finset.sum_product_right P C (fun xb : α × β ↦
    if R xb.1 xb.2 then (1 : ℕ) else 0)).symm

private theorem inline_Esgk_FiniteIncidenceCodegreeBound__finiteIncidence_secondMoment_le {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) (M : ℕ)
    (hcodegree : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      (C.filter (fun b ↦ R x b ∧ R y b)).card ≤ M) :
    ∑ b ∈ C, (P.filter (fun x ↦ R x b)).card ^ 2 ≤
      finiteIncidenceCount P C R + M * P.card ^ 2 := by
  classical
  let w : α → β → ℕ := fun x b ↦ if R x b then 1 else 0
  let common : α → α → ℕ := fun x y ↦
    (C.filter (fun b ↦ R x b ∧ R y b)).card
  have hdegree (b : β) : (P.filter (fun x ↦ R x b)).card =
      ∑ x ∈ P, w x b := by
    exact Finset.card_filter _ _
  have hcommon (x y : α) : common x y = ∑ b ∈ C, w x b * w y b := by
    change (C.filter (fun b ↦ R x b ∧ R y b)).card = _
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [w]
    split_ifs <;> simp_all
  have hdouble :
      (∑ b ∈ C, (P.filter (fun x ↦ R x b)).card ^ 2) =
      ∑ x ∈ P, ∑ y ∈ P, common x y := by
    simp_rw [hdegree, pow_two, Finset.sum_mul, Finset.mul_sum, hcommon]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.sum_comm]
  have hpoint (x : α) (hx : x ∈ P) :
      ∑ y ∈ P, common x y ≤ (C.filter (fun b ↦ R x b)).card + M * P.card := by
    calc
      ∑ y ∈ P, common x y ≤
          ∑ y ∈ P, ((if x = y then (C.filter (fun b ↦ R x b)).card else 0) + M) := by
        apply Finset.sum_le_sum
        intro y hy
        by_cases hxy : x = y
        · subst y
          simp [common]
        · simpa [hxy, common] using hcodegree x hx y hy hxy
      _ = (C.filter (fun b ↦ R x b)).card + M * P.card := by
        simp [Finset.sum_add_distrib, hx, eq_comm, Nat.mul_comm]
  have hcount : (∑ x ∈ P, (C.filter (fun b ↦ R x b)).card) =
      finiteIncidenceCount P C R := by
    simp only [finiteIncidenceCount, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hdouble]
  calc
    (∑ x ∈ P, ∑ y ∈ P, common x y) ≤
        ∑ x ∈ P, ((C.filter (fun b ↦ R x b)).card + M * P.card) :=
      Finset.sum_le_sum hpoint
    _ = finiteIncidenceCount P C R + M * P.card ^ 2 := by
      rw [Finset.sum_add_distrib, hcount]
      simp only [Finset.sum_const, smul_eq_mul]
      ring

theorem finiteIncidenceCount_sq_le_of_codegree {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) (M : ℕ)
    (hcodegree : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      (C.filter (fun b ↦ R x b ∧ R y b)).card ≤ M) :
    finiteIncidenceCount P C R ^ 2 ≤
      C.card * finiteIncidenceCount P C R + M * C.card * P.card ^ 2 := by
  calc
    finiteIncidenceCount P C R ^ 2 ≤
        C.card * ∑ b ∈ C, (P.filter (fun x ↦ R x b)).card ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ C.card * (finiteIncidenceCount P C R + M * P.card ^ 2) :=
      Nat.mul_le_mul_left _ (inline_Esgk_FiniteIncidenceCodegreeBound__finiteIncidence_secondMoment_le P C R M hcodegree)
    _ = C.card * finiteIncidenceCount P C R + M * C.card * P.card ^ 2 := by ring

theorem finiteIncidenceCount_le_of_codegree {α β : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop) (M : ℕ)
    (hcodegree : ∀ x ∈ P, ∀ y ∈ P, x ≠ y →
      (C.filter (fun b ↦ R x b ∧ R y b)).card ≤ M) :
    (finiteIncidenceCount P C R : ℝ) ≤
      (C.card : ℝ) + Real.sqrt M * P.card * Real.sqrt C.card := by
  have hquad : (finiteIncidenceCount P C R : ℝ) ^ 2 ≤
      (C.card : ℝ) * finiteIncidenceCount P C R +
        (M : ℝ) * C.card * (P.card : ℝ) ^ 2 := by
    exact_mod_cast finiteIncidenceCount_sq_le_of_codegree P C R M hcodegree
  let s : ℝ := Real.sqrt M * P.card * Real.sqrt C.card
  have hs : 0 ≤ s := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  have hsq : s ^ 2 = (M : ℝ) * C.card * (P.card : ℝ) ^ 2 := by
    dsimp [s]
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    ring
  change (finiteIncidenceCount P C R : ℝ) ≤ (C.card : ℝ) + s
  by_contra h
  have hgap : 0 < (finiteIncidenceCount P C R : ℝ) - C.card - s := by linarith
  have hI : 0 < (finiteIncidenceCount P C R : ℝ) := by
    have hc : 0 ≤ (C.card : ℝ) := Nat.cast_nonneg _
    linarith
  have hIs : 0 ≤ (finiteIncidenceCount P C R : ℝ) - s := by
    have hc : 0 ≤ (C.card : ℝ) := Nat.cast_nonneg _
    linarith
  nlinarith [mul_pos hgap hI, mul_nonneg hs hIs]


theorem finiteCellIncidenceSum_le {ι : Type*}
    (cells : Finset ι) (I h g : ι → ℕ) (M : ℕ) (L R T : ℝ)
    (hL : 0 ≤ L) (hR : (cells.card : ℝ) ≤ R)
    (hT : (∑ ω ∈ cells, (g ω : ℝ)) ≤ T)
    (hpoints : ∀ ω ∈ cells, (h ω : ℝ) ≤ L)
    (hlocal : ∀ ω ∈ cells, (I ω : ℝ) ≤
      Real.sqrt M * h ω * Real.sqrt (g ω) + g ω) :
    (∑ ω ∈ cells, (I ω : ℝ)) ≤ Real.sqrt M * L * Real.sqrt (R * T) + T := by
  have hR0 : 0 ≤ R := (Nat.cast_nonneg cells.card).trans hR
  have hsumg0 : 0 ≤ ∑ ω ∈ cells, (g ω : ℝ) :=
    Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  have hsqrtSum : (∑ ω ∈ cells, Real.sqrt (g ω)) ≤ Real.sqrt (R * T) := by
    calc
      (∑ ω ∈ cells, Real.sqrt (g ω)) ≤
          Real.sqrt (cells.card : ℝ) * Real.sqrt (∑ ω ∈ cells, (g ω : ℝ)) := by
        simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
          Real.sq_sqrt (Nat.cast_nonneg _)] using
          Real.sum_mul_le_sqrt_mul_sqrt cells (fun _ ↦ (1 : ℝ))
            (fun ω ↦ Real.sqrt (g ω))
      _ = Real.sqrt ((cells.card : ℝ) * ∑ ω ∈ cells, (g ω : ℝ)) :=
        (Real.sqrt_mul (Nat.cast_nonneg _) _).symm
      _ ≤ Real.sqrt (R * T) :=
        Real.sqrt_le_sqrt (mul_le_mul hR hT hsumg0 hR0)
  calc
    (∑ ω ∈ cells, (I ω : ℝ)) ≤
        ∑ ω ∈ cells, (Real.sqrt M * L * Real.sqrt (g ω) + g ω) := by
      apply Finset.sum_le_sum
      intro ω hω
      exact (hlocal ω hω).trans (add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpoints ω hω) (Real.sqrt_nonneg _))
          (Real.sqrt_nonneg _)) le_rfl)
    _ = Real.sqrt M * L * (∑ ω ∈ cells, Real.sqrt (g ω)) +
        ∑ ω ∈ cells, (g ω : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ Real.sqrt M * L * Real.sqrt (R * T) + T :=
      add_le_add (mul_le_mul_of_nonneg_left hsqrtSum
        (mul_nonneg (Real.sqrt_nonneg _) hL)) hT

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk


private theorem inline_Esgk_FiniteRealCutIntervals__isOpen_below_finset (T : Finset ℝ) :
    IsOpen {x : ℝ | ∀ t ∈ T, x < t} := by
  convert isOpen_biInter_finset (s := T) (f := fun t ↦ Iio t)
    (fun _ _ ↦ isOpen_Iio) using 1
  ext x
  simp

 
theorem isOpen_realCutInterval {J : Set ℝ} (hJ : IsOpen J)
    (T : Finset ℝ) (o : Option {t // t ∈ T}) : IsOpen (realCutInterval J T o) := by
  cases o with
  | none => exact hJ.inter (inline_Esgk_FiniteRealCutIntervals__isOpen_below_finset T)
  | some c =>
      have heq : realCutInterval J T (some c) =
          (J ∩ Ioi (c : ℝ)) ∩ {x | ∀ t ∈ T.filter (fun t ↦ (c : ℝ) < t), x < t} := by
        ext x
        simp [realCutInterval, and_assoc]
        tauto
      rw [heq]
      exact (hJ.inter isOpen_Ioi).inter (inline_Esgk_FiniteRealCutIntervals__isOpen_below_finset _)

 
theorem ordConnected_realCutInterval {J : Set ℝ} (hJ : J.OrdConnected)
    (T : Finset ℝ) (o : Option {t // t ∈ T}) : (realCutInterval J T o).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  cases o with
  | none =>
      exact ⟨hJ.out hx.1 hy.1 hz, fun t ht ↦ hz.2.trans_lt (hy.2 t ht)⟩
  | some c =>
      exact ⟨hJ.out hx.1 hy.1 hz, hx.2.1.trans_le hz.1,
        fun t ht hct ↦ hz.2.trans_lt (hy.2.2 t ht hct)⟩

 
theorem realCutInterval_subset (J : Set ℝ) (T : Finset ℝ)
    (o : Option {t // t ∈ T}) : realCutInterval J T o ⊆ J := by
  cases o <;> exact fun _ h ↦ h.1

 
theorem isConnected_realCutInterval {J : Set ℝ} (hJ : J.OrdConnected)
    (T : Finset ℝ) (o : Option {t // t ∈ T})
    (hne : (realCutInterval J T o).Nonempty) :
    IsConnected (realCutInterval J T o) :=
  ⟨hne, (ordConnected_realCutInterval hJ T o).isPreconnected⟩

 
theorem disjoint_realCutInterval_cuts (J : Set ℝ) (T : Finset ℝ)
    (o : Option {t // t ∈ T}) : Disjoint (realCutInterval J T o) (T : Set ℝ) := by
  apply Set.disjoint_left.mpr
  intro x hx hxT
  cases o with
  | none => exact (lt_irrefl x) (hx.2 x hxT)
  | some c => exact (lt_irrefl x) (hx.2.2 x hxT hx.2.1)

 
theorem pairwise_disjoint_realCutInterval (J : Set ℝ) (T : Finset ℝ) :
    Pairwise (fun i j : Option {t // t ∈ T} ↦
      Disjoint (realCutInterval J T i) (realCutInterval J T j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases i with
  | none =>
      cases j with
      | none => exact hij rfl
      | some d => exact lt_asymm (hx.2 d d.property) hy.2.1
  | some c =>
      cases j with
      | none => exact lt_asymm hx.2.1 (hy.2 c c.property)
      | some d =>
          rcases lt_trichotomy (c : ℝ) (d : ℝ) with hcd | hcd | hdc
          · exact lt_asymm (hx.2.2 d d.property hcd) hy.2.1
          · exact hij (congrArg some (Subtype.ext hcd))
          · exact lt_asymm (hy.2.2 c c.property hdc) hx.2.1

 
theorem exists_mem_realCutInterval {J : Set ℝ} (T : Finset ℝ) {x : ℝ}
    (hxJ : x ∈ J) (hxT : x ∉ T) :
    ∃ o : Option {t // t ∈ T}, x ∈ realCutInterval J T o := by
  let D := T.filter (fun t ↦ t < x)
  by_cases hD : D.Nonempty
  · let c := D.max' hD
    have hcD : c ∈ D := D.max'_mem hD
    have hcT : c ∈ T := (Finset.mem_filter.mp hcD).1
    have hcx : c < x := (Finset.mem_filter.mp hcD).2
    refine ⟨some ⟨c, hcT⟩, hxJ, hcx, ?_⟩
    intro t ht hct
    by_contra hxt
    have htle : t ≤ x := le_of_not_gt hxt
    have htne : t ≠ x := by
      intro heq
      apply hxT
      simpa only [heq] using ht
    have htD : t ∈ D := Finset.mem_filter.mpr ⟨ht, lt_of_le_of_ne htle htne⟩
    exact not_lt_of_ge (D.le_max' t htD) hct
  · refine ⟨none, hxJ, ?_⟩
    intro t ht
    by_contra hxt
    have htle : t ≤ x := le_of_not_gt hxt
    have htne : t ≠ x := by
      intro heq
      apply hxT
      simpa only [heq] using ht
    exact hD ⟨t, Finset.mem_filter.mpr ⟨ht, lt_of_le_of_ne htle htne⟩⟩

 
theorem frontier_realCutInterval_subset {J : Set ℝ} (hJ : IsOpen J)
    (T : Finset ℝ) (o : Option {t // t ∈ T}) :
    frontier (realCutInterval J T o) ⊆ frontier J ∪ (T : Set ℝ) := by
  intro x hx
  by_contra hbad
  have hxnotF : x ∉ frontier J := fun h ↦ hbad (Or.inl h)
  have hxnotT : x ∉ T := fun h ↦ hbad (Or.inr h)
  have hxclosure : x ∈ closure (realCutInterval J T o) := frontier_subset_closure hx
  have hxnot : x ∉ realCutInterval J T o := by
    rw [(isOpen_realCutInterval hJ T o).frontier_eq] at hx
    exact hx.2
  have hxJ : x ∈ J := by
    by_contra hxJ
    apply hxnotF
    rw [hJ.frontier_eq]
    exact ⟨closure_mono (realCutInterval_subset J T o) hxclosure, hxJ⟩
  obtain ⟨o', hxo'⟩ := exists_mem_realCutInterval T hxJ hxnotT
  have hoo' : o ≠ o' := by
    intro heq
    apply hxnot
    simpa only [heq] using hxo'
  obtain ⟨y, hyo', hyo⟩ := mem_closure_iff.mp hxclosure
    (realCutInterval J T o') (isOpen_realCutInterval hJ T o') hxo'
  exact Set.disjoint_left.mp (pairwise_disjoint_realCutInterval J T hoo') hyo hyo'


theorem exists_finite_real_cut_intervals (J : Set ℝ) (T : Finset ℝ)
    (hJopen : IsOpen J) (hJord : J.OrdConnected) :
    ∃ A : Finset (Set ℝ), A.card ≤ T.card + 1 ∧
      (∀ I ∈ A, I.Nonempty ∧ IsOpen I ∧ IsConnected I ∧ I.OrdConnected ∧ I ⊆ J ∧
        Disjoint I (T : Set ℝ) ∧ frontier I ⊆ frontier J ∪ (T : Set ℝ)) ∧
      (A : Set (Set ℝ)).Pairwise Disjoint ∧
      (⋃ I ∈ A, I) = J \ (T : Set ℝ) := by
  classical
  let A := (Finset.univ.image (realCutInterval J T)).filter Set.Nonempty
  have hmem : ∀ I ∈ A, ∃ o, I = realCutInterval J T o := by
    intro I hI
    obtain ⟨o, _, ho⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hI).1
    exact ⟨o, ho.symm⟩
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · calc
      A.card ≤ (Finset.univ.image (realCutInterval J T)).card := Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Option {t // t ∈ T})).card := Finset.card_image_le
      _ = T.card + 1 := by simp
  · intro I hI
    obtain ⟨o, rfl⟩ := hmem I hI
    exact ⟨(Finset.mem_filter.mp hI).2, isOpen_realCutInterval hJopen T o,
      isConnected_realCutInterval hJord T o (Finset.mem_filter.mp hI).2,
      ordConnected_realCutInterval hJord T o, realCutInterval_subset J T o,
      disjoint_realCutInterval_cuts J T o, frontier_realCutInterval_subset hJopen T o⟩
  · intro I hI K hK hne
    obtain ⟨o, rfl⟩ := hmem I hI
    obtain ⟨o', rfl⟩ := hmem K hK
    apply pairwise_disjoint_realCutInterval J T
    intro heq
    exact hne (congrArg (realCutInterval J T) heq)
  · ext x
    simp only [Set.mem_iUnion, Set.mem_sdiff, Finset.mem_coe]
    constructor
    · rintro ⟨I, hI, hx⟩
      obtain ⟨o, rfl⟩ := hmem I hI
      exact ⟨realCutInterval_subset J T o hx,
        fun hxT ↦ Set.disjoint_left.mp (disjoint_realCutInterval_cuts J T o) hx hxT⟩
    · rintro ⟨hxJ, hxT⟩
      obtain ⟨o, hxo⟩ := exists_mem_realCutInterval T hxJ hxT
      refine ⟨realCutInterval J T o, ?_, hxo⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨o, Finset.mem_univ _, rfl⟩, ⟨x, hxo⟩⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open scoped Classical

private lemma inline_Esgk_FiniteRealSampleCuts__finiteRealSampleCuts_index
    {n k : ℕ} (hk : 0 < k) {a b : Fin n}
    (hab : k ≤ b.1 - a.1) :
    ∃ j : Fin ((n - 1) / k),
      a.1 < (j.1 + 1) * k ∧ (j.1 + 1) * k ≤ b.1 := by
  have ha : a.1 < n := a.2
  have hb : b.1 < n := b.2
  have hab' : a.1 + k ≤ b.1 := by omega
  let q : ℕ := a.1 / k
  have hqstrict : a.1 < (q + 1) * k := by
    simpa [q, Nat.mul_comm] using Nat.lt_mul_div_succ a.1 hk
  have hqbound : (q + 1) * k ≤ b.1 := by
    have hle : (q + 1) * k ≤ a.1 + k := by
      dsimp [q]
      calc
        (a.1 / k + 1) * k = a.1 / k * k + k := by ring
        _ ≤ a.1 + k := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    exact hle.trans hab'
  have hqfin' : q < (n - 1) / k := by
    rw [Nat.lt_div_iff_mul_lt hk]
    have hmul : q * k + k < n := by
      simpa [Nat.add_mul] using hqbound.trans_lt hb
    omega
  exact ⟨⟨q, hqfin'⟩, hqstrict, hqbound⟩

theorem exists_finite_real_sample_cuts
    (S : Finset ℝ) (k : ℕ) (hk : 0 < k) :
    ∃ T : Finset ℝ,
      T.card ≤ S.card / k ∧
      Disjoint S T ∧
      (∀ t ∈ T, ∃ a ∈ S, ∃ b ∈ S, a < t ∧ t < b) ∧
      (∀ J : Set ℝ, J.OrdConnected → Disjoint J (T : Set ℝ) →
        (S.filter (fun x ↦ x ∈ J)).card ≤ k) := by
  classical
  let n := S.card
  let q := (n - 1) / k
  let f : Fin n ↪o ℝ := S.orderEmbOfFin rfl
  have hn_of_index (j : Fin q) : 0 < n := by
    have hj := j.isLt
    by_contra hn
    have hnzero : n = 0 := by omega
    simp [q, hnzero] at hj
  let left : Fin q → Fin n := fun j =>
    ⟨(j.1 + 1) * k - 1, by
      have hq : (j.1 + 1) * k ≤ q * k := by
        exact Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.2)
      have hqn : q * k < n := by
        have hn := hn_of_index j
        dsimp [q]
        have hle := Nat.div_mul_le_self (n - 1) k
        omega
      omega⟩
  let right : Fin q → Fin n := fun j =>
    ⟨(j.1 + 1) * k, by
      have hq : (j.1 + 1) * k ≤ q * k := by
        exact Nat.mul_le_mul_right k (Nat.succ_le_of_lt j.2)
      have hqn : q * k < n := by
        have hn := hn_of_index j
        dsimp [q]
        have hle := Nat.div_mul_le_self (n - 1) k
        omega
      omega⟩
  let midpoint : Fin q → ℝ := fun j => (f (left j) + f (right j)) / 2
  let T : Finset ℝ := Finset.univ.image midpoint
  have hleft_lt_right (j : Fin q) : left j < right j := by
    change (j.1 + 1) * k - 1 < (j.1 + 1) * k
    have : 0 < (j.1 + 1) * k := Nat.mul_pos (Nat.succ_pos _) hk
    omega
  have hmidpoint_between (j : Fin q) :
      f (left j) < midpoint j ∧ midpoint j < f (right j) := by
    dsimp [midpoint]
    have hlt := f.strictMono (hleft_lt_right j)
    constructor <;> linarith
  have hTcard : T.card ≤ q := by
    calc
      T.card ≤ (Finset.univ : Finset (Fin q)).card := by
        exact Finset.card_image_le
      _ = q := by simp
  have hTbetween (t : ℝ) (ht : t ∈ T) :
      ∃ a ∈ S, ∃ b ∈ S, a < t ∧ t < b := by
    rcases Finset.mem_image.mp ht with ⟨j, -, rfl⟩
    refine ⟨f (left j), S.orderEmbOfFin_mem rfl _, f (right j),
      S.orderEmbOfFin_mem rfl _, (hmidpoint_between j).1, (hmidpoint_between j).2⟩
  have hTdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    rcases Finset.mem_image.mp hxT with ⟨j, -, hjt⟩
    have hxS' : x ∈ Finset.image (S.orderEmbOfFin rfl) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hxS
    rcases Finset.mem_image.mp hxS' with ⟨i, -, hix⟩
    have hmid : f i = midpoint j := hix.trans hjt.symm
    have hli : left j < i := by
      by_contra hnot
      have hi : i ≤ left j := le_of_not_gt hnot
      have := f.monotone hi
      linarith [hmidpoint_between j |>.1, hmid]
    have hir : i < right j := by
      by_contra hnot
      have hi : right j ≤ i := le_of_not_gt hnot
      have := f.monotone hi
      linarith [hmidpoint_between j |>.2, hmid]
    have hgap : (left j).1 + 1 = (right j).1 := by
      dsimp [left, right]
      have : 0 < (j.1 + 1) * k := Nat.mul_pos (Nat.succ_pos _) hk
      omega
    omega
  refine ⟨T, ?_, hTdisjoint, hTbetween, ?_⟩
  · calc
      T.card ≤ q := hTcard
      _ ≤ n / k := by
        apply Nat.div_le_div_right
        omega
  intro J hJ hJT
  let U : Finset ℝ := S.filter (fun x ↦ x ∈ J)
  by_contra hU
  have hUcard : k < U.card := Nat.lt_of_not_ge hU
  let I : Finset (Fin n) := Finset.univ.filter (fun i ↦ f i ∈ J)
  have hIcard : I.card = U.card := by
    apply Finset.card_bij (fun i _ ↦ f i)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl i,
        Finset.mem_filter.mp hi |>.2⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact f.injective heq
    · intro x hx
      have hxS : x ∈ S := Finset.mem_filter.mp hx |>.1
      have hximage : x ∈ Finset.image (S.orderEmbOfFin rfl) Finset.univ := by
        rw [Finset.image_orderEmbOfFin_univ]
        exact hxS
      rcases Finset.mem_image.mp hximage with ⟨i, -, hix⟩
      refine ⟨i, ?_, hix⟩
      have hix' : f i = x := hix
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [hix'] using
        (Finset.mem_filter.mp hx).2⟩
  have hIcard' : k < I.card := by
    rw [hIcard]
    exact hUcard
  have hInonempty : I.Nonempty := by
    exact Finset.nonempty_of_ne_empty (by
      intro h
      simp [h] at hIcard')
  let a : Fin n := I.min' hInonempty
  let b : Fin n := I.max' hInonempty
  have habI : Finset.Icc a b ⊆ I := by
    intro i hi
    rcases Finset.mem_Icc.mp hi with ⟨hai', hib'⟩
    have hai : f a ≤ f i := f.monotone hai'
    have hib : f i ≤ f b := f.monotone hib'
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact hJ.out (Finset.mem_filter.mp (I.min'_mem hInonempty)).2
      (Finset.mem_filter.mp (I.max'_mem hInonempty)).2 ⟨hai, hib⟩
  have hIab : I ⊆ Finset.Icc a b := by
    intro i hi
    apply Finset.mem_Icc.mpr
    exact ⟨by simpa [a] using I.min'_le i hi,
      by simpa [b] using I.le_max' i hi⟩
  have hIcc_eq : I = Finset.Icc a b := by
    apply Finset.ext
    intro i
    exact ⟨fun h ↦ hIab h, fun h ↦ habI h⟩
  have hgap : k ≤ b.1 - a.1 := by
    have hcardIcc : k < (Finset.Icc a b).card := by
      rw [← hIcc_eq]
      exact hIcard'
    simp only [Fin.card_Icc] at hcardIcc
    omega
  obtain ⟨j, hjlo, hjhi⟩ := inline_Esgk_FiniteRealSampleCuts__finiteRealSampleCuts_index hk hgap
  have hleftI : left j ∈ I := by
    apply habI
    rw [Finset.mem_Icc]
    change a.1 ≤ (j.1 + 1) * k - 1 ∧ (j.1 + 1) * k - 1 ≤ b.1
    constructor <;> omega
  have hrightI : right j ∈ I := by
    apply habI
    rw [Finset.mem_Icc]
    change a.1 ≤ (j.1 + 1) * k ∧ (j.1 + 1) * k ≤ b.1
    constructor <;> omega
  have hmidJ : midpoint j ∈ J := by
    apply hJ.out (Finset.mem_filter.mp hleftI).2 (Finset.mem_filter.mp hrightI).2
    exact ⟨(hmidpoint_between j).1.le, (hmidpoint_between j).2.le⟩
  exact (Set.disjoint_left.1 hJT) hmidJ
    (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

 
private lemma inline_Esgk_IntrinsicCellIncidenceArithmetic__intrinsicCell_sqrt_eighty_sq_le (d : ℝ) (hd : 0 < d) :
    Real.sqrt (80 * d ^ 2) ≤ 9 * d := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have hs0 : 0 ≤ Real.sqrt (80 * d ^ 2) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (80 * d ^ 2)) ^ 2 = 80 * d ^ 2 := by
    exact Real.sq_sqrt (by positivity)
  have hbound : 80 * d ^ 2 ≤ (9 * d) ^ 2 := by
    nlinarith [sq_nonneg d]
  by_contra hnot
  have hgt : 9 * d < Real.sqrt (80 * d ^ 2) := lt_of_not_ge hnot
  have hsum : 0 < Real.sqrt (80 * d ^ 2) + 9 * d := by
    nlinarith
  have hprod : 0 <
      (Real.sqrt (80 * d ^ 2) - 9 * d) *
        (Real.sqrt (80 * d ^ 2) + 9 * d) :=
    mul_pos (sub_pos.mpr hgt) hsum
  nlinarith [hprod]

 
private lemma inline_Esgk_IntrinsicCellIncidenceArithmetic__intrinsicCell_sqrt_radial_sq_le (d j N : ℝ)
    (hd : 0 < d) (hj : 0 < j) (hN : 0 ≤ N) :
    Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)) ≤
      (20 / 3 : ℝ) * d ^ 2 * j * Real.sqrt j * N := by
  let R : ℝ := (2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)
  let T : ℝ := (20 / 3 : ℝ) * d ^ 2 * j * Real.sqrt j * N
  have hd0 : 0 ≤ d := le_of_lt hd
  have hj0 : 0 ≤ j := le_of_lt hj
  have hsqrtj0 : 0 ≤ Real.sqrt j := Real.sqrt_nonneg _
  have hsqrtj2 : (Real.sqrt j) ^ 2 = j := Real.sq_sqrt hj0
  have hR0 : 0 ≤ R := by
    dsimp [R]
    positivity
  have hs0 : 0 ≤ Real.sqrt R := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt R) ^ 2 = R := Real.sq_sqrt hR0
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hT2 : T ^ 2 = (400 / 9 : ℝ) * d ^ 4 * j ^ 3 * N ^ 2 := by
    dsimp [T]
    calc
      ((20 / 3 : ℝ) * d ^ 2 * j * Real.sqrt j * N) ^ 2 =
          (20 / 3 : ℝ) ^ 2 * (d ^ 2) ^ 2 * j ^ 2 *
            (Real.sqrt j) ^ 2 * N ^ 2 := by ring
      _ = (400 / 9 : ℝ) * d ^ 4 * j ^ 3 * N ^ 2 := by
        rw [hsqrtj2]
        ring
  have hRle : R ≤ T ^ 2 := by
    rw [hT2]
    dsimp [R]
    have hprod : 0 ≤ d ^ 4 * j ^ 3 * N ^ 2 := by positivity
    nlinarith
  change Real.sqrt R ≤ T
  by_contra hnot
  have hgt : T < Real.sqrt R := lt_of_not_ge hnot
  have hsum : 0 < Real.sqrt R + T := by
    nlinarith
  have hprod : 0 < (Real.sqrt R - T) * (Real.sqrt R + T) :=
    mul_pos (sub_pos.mpr hgt) hsum
  nlinarith [hprod]


theorem intrinsicCellIncidence_sqrt_product_le
    (d j N : ℝ) (hd : 0 < d) (hj : 0 < j) (hN : 0 ≤ N) :
    Real.sqrt (80 * d ^ 2) * (4 * N ^ 2 / (d ^ 2 * j ^ 2)) *
        Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)) ≤
      240 * d * N ^ 3 / Real.sqrt j := by
  have hsqrtj : 0 < Real.sqrt j := Real.sqrt_pos.2 hj
  have h80 := inline_Esgk_IntrinsicCellIncidenceArithmetic__intrinsicCell_sqrt_eighty_sq_le d hd
  have hrad := inline_Esgk_IntrinsicCellIncidenceArithmetic__intrinsicCell_sqrt_radial_sq_le d j N hd hj hN
  have hrad0 : 0 ≤ Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)) :=
    Real.sqrt_nonneg _
  have hmid : 0 ≤ 4 * N ^ 2 / (d ^ 2 * j ^ 2) := by positivity
  have hleft : 0 ≤ 9 * d * (4 * N ^ 2 / (d ^ 2 * j ^ 2)) := by positivity
  calc
    Real.sqrt (80 * d ^ 2) * (4 * N ^ 2 / (d ^ 2 * j ^ 2)) *
          Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)) =
        Real.sqrt (80 * d ^ 2) *
          ((4 * N ^ 2 / (d ^ 2 * j ^ 2)) *
            Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2))) := by ring
    _ ≤ 9 * d *
          ((4 * N ^ 2 / (d ^ 2 * j ^ 2)) *
            Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2))) := by
      exact mul_le_mul_of_nonneg_right h80 (mul_nonneg hmid hrad0)
    _ = (9 * d * (4 * N ^ 2 / (d ^ 2 * j ^ 2))) *
          Real.sqrt ((2 * d ^ 2 * j ^ 2) * (20 * d ^ 2 * j * N ^ 2)) := by ring
    _ ≤ (9 * d * (4 * N ^ 2 / (d ^ 2 * j ^ 2))) *
          ((20 / 3 : ℝ) * d ^ 2 * j * Real.sqrt j * N) := by
      exact mul_le_mul_of_nonneg_left hrad hleft
    _ = 240 * d * N ^ 3 / Real.sqrt j := by
      field_simp [ne_of_gt hd, ne_of_gt hj, ne_of_gt hsqrtj]
      rw [Real.sq_sqrt hj.le]
      ring


theorem intrinsicCellIncidence_scale_sum_le
    (d j N : ℝ) (hd : 0 < d) (hj : 0 < j) (hN : 0 ≤ N) :
    240 * d * N ^ 3 / Real.sqrt j + 20 * d ^ 2 * j * N ^ 2 + 24 * d ^ 3 * N ^ 2 ≤
      256 * (d * N ^ 3 / Real.sqrt j + d ^ 2 * j * N ^ 2 + N ^ 2 +
        d ^ 4 * j ^ 2 + d ^ 3 * N ^ 2) := by
  have hsqrtj : 0 < Real.sqrt j := Real.sqrt_pos.2 hj
  let A : ℝ := d * N ^ 3 / Real.sqrt j
  let B : ℝ := d ^ 2 * j * N ^ 2
  let C : ℝ := N ^ 2
  let D : ℝ := d ^ 4 * j ^ 2
  let degreeRight : ℝ := d ^ 3 * N ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact sq_nonneg N
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hE : 0 ≤ degreeRight := by
    dsimp [degreeRight]
    positivity
  have hlinear : 240 * A + 20 * B + 24 * degreeRight ≤ 256 * (A + B + C + D + degreeRight) := by
    linarith
  simpa [A, B, C, D, degreeRight, add_assoc, mul_assoc, div_eq_mul_inv] using hlinear

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open Set Metric


theorem exists_minimizing_equalDistance_pair
    {α β : Type*} [MetricSpace α] [MetricSpace β] [ProperSpace α] [ProperSpace β]
    (a : α) (b : β) (A : Set α) (B : Set β)
    (hne : ∃ x ∈ A, ∃ y ∈ B, dist x a = dist y b) :
    ∃ x ∈ closure A, ∃ y ∈ closure B, dist x a = dist y b ∧
      ∀ x' ∈ A, ∀ y' ∈ B, dist x' a = dist y' b → dist x a ≤ dist x' a := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy₀⟩ := hne
  let degreeRight : Set (α × β) := {z | z.1 ∈ A ∧ z.2 ∈ B ∧ dist z.1 a = dist z.2 b}
  let r := dist x₀ a
  let K := closure degreeRight ∩ (closedBall a r ×ˢ closedBall b r)
  have hE₀ : (x₀, y₀) ∈ degreeRight := ⟨hx₀, hy₀, hxy₀⟩
  have hK₀ : (x₀, y₀) ∈ K := by
    refine ⟨subset_closure hE₀, ?_, ?_⟩
    · change dist x₀ a ≤ dist x₀ a
      exact le_rfl
    · change dist y₀ b ≤ dist x₀ a
      exact hxy₀.ge
  have hK : IsCompact K :=
    ((isCompact_closedBall a r).prod (isCompact_closedBall b r)).inter_left isClosed_closure
  have hA : closure degreeRight ⊆ {z : α × β | z.1 ∈ closure A} := by
    apply closure_minimal _ (isClosed_closure.preimage continuous_fst)
    intro z hz
    exact subset_closure hz.1
  have hB : closure degreeRight ⊆ {z : α × β | z.2 ∈ closure B} := by
    apply closure_minimal _ (isClosed_closure.preimage continuous_snd)
    intro z hz
    exact subset_closure hz.2.1
  have heq : closure degreeRight ⊆ {z : α × β | dist z.1 a = dist z.2 b} := by
    apply closure_minimal _ (isClosed_eq
      (continuous_fst.dist continuous_const) (continuous_snd.dist continuous_const))
    intro z hz
    exact hz.2.2
  have hcont : Continuous (fun z : α × β ↦ dist z.1 a) :=
    continuous_fst.dist continuous_const
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn ⟨(x₀, y₀), hK₀⟩ hcont.continuousOn
  refine ⟨z.1, hA hz.1, z.2, hB hz.1, heq hz.1, ?_⟩
  intro x' hx' y' hy' hxy'
  by_cases hr : dist x' a ≤ r
  · have hmem : (x', y') ∈ K := by
      refine ⟨subset_closure (show (x', y') ∈ degreeRight from ⟨hx', hy', hxy'⟩), hr, ?_⟩
      change dist y' b ≤ r
      rwa [← hxy']
    exact (isMinOn_iff.mp hmin) (x', y') hmem
  · exact le_trans hz.2.1 (le_of_not_ge hr)


theorem exists_equalSqDistance_boundary_or_critical_witness
    {α β : Type*} [MetricSpace α] [MetricSpace β] [ProperSpace α] [ProperSpace β]
    (a : α) (b : β) (A : Set α) (B : Set β) (criticalA : Set α) (criticalB : Set β)
    (hne : ∃ x ∈ A, ∃ y ∈ B, dist x a ^ 2 = dist y b ^ 2)
    (hlocalA : ∀ x ∈ A, x ∉ criticalA →
      dist x a ^ 2 ∈ interior ((fun u ↦ dist u a ^ 2) '' A))
    (hlocalB : ∀ y ∈ B, y ∉ criticalB →
      dist y b ^ 2 ∈ interior ((fun v ↦ dist v b ^ 2) '' B)) :
    ∃ x ∈ closure A, ∃ y ∈ closure B, dist x a ^ 2 = dist y b ^ 2 ∧
      (x ∈ (closure A \ A) ∪ criticalA ∨ y ∈ (closure B \ B) ∪ criticalB) := by
  have hne' : ∃ x ∈ A, ∃ y ∈ B, dist x a = dist y b := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hne
    exact ⟨x, hx, y, hy, (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hxy⟩
  obtain ⟨x, hx, y, hy, hxy, hmin⟩ := exists_minimizing_equalDistance_pair a b A B hne'
  refine ⟨x, hx, y, hy, congrArg (fun t : ℝ ↦ t ^ 2) hxy, ?_⟩
  by_contra hbad
  have hxA : x ∈ A := by
    by_contra hxA
    exact hbad (Or.inl (Or.inl ⟨hx, hxA⟩))
  have hyB : y ∈ B := by
    by_contra hyB
    exact hbad (Or.inr (Or.inl ⟨hy, hyB⟩))
  have hxcrit : x ∉ criticalA := fun h ↦ hbad (Or.inl (Or.inr h))
  have hycrit : y ∉ criticalB := fun h ↦ hbad (Or.inr (Or.inr h))
  let U := interior ((fun u ↦ dist u a ^ 2) '' A) ∩ interior ((fun v ↦ dist v b ^ 2) '' B)
  have hU : IsOpen U := isOpen_interior.inter isOpen_interior
  have hrU : dist x a ^ 2 ∈ U := by
    refine ⟨hlocalA x hxA hxcrit, ?_⟩
    rw [hxy]
    exact hlocalB y hyB hycrit
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (dist x a ^ 2) hrU
  let s := dist x a ^ 2 - ε / 2
  have hs : s ∈ ball (dist x a ^ 2) ε := by
    rw [mem_ball, Real.dist_eq, abs_of_nonpos]
    · dsimp [s]
      linarith
    · dsimp [s]
      linarith
  obtain ⟨x', hx', hxs⟩ := interior_subset (hball hs).1
  obtain ⟨y', hy', hys⟩ := interior_subset (hball hs).2
  change dist x' a ^ 2 = s at hxs
  change dist y' b ^ 2 = s at hys
  have hdist : dist x' a = dist y' b :=
    (sq_eq_sq₀ dist_nonneg dist_nonneg).mp (hxs.trans hys.symm)
  have hbound := hmin x' hx' y' hy' hdist
  have hsquare : dist x a ^ 2 ≤ dist x' a ^ 2 :=
    pow_le_pow_left₀ dist_nonneg hbound 2
  rw [hxs] at hsquare
  dsimp [s] at hsquare
  linarith

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk


private theorem inline_Esgk_IntrinsicPartitionScale__intrinsicCeilingQuotient_bounds {q N : ℕ}
    (hq : 0 < q) (hN : q < N) :
    let k := (N + q - 1) / q
    0 < k ∧ N ≤ k * q ∧ k * q ≤ 2 * N ∧ N / k ≤ q := by
  dsimp only
  let k := (N + q - 1) / q
  have hlower : N ≤ k * q := by
    have hmod := Nat.mod_lt (N + q - 1) hq
    have hdiv := Nat.mod_add_div' (N + q - 1) q
    change (N + q - 1) % q + k * q = N + q - 1 at hdiv
    omega
  have hupper : k * q ≤ 2 * N := by
    have hdiv := Nat.div_mul_le_self (N + q - 1) q
    change k * q ≤ N + q - 1 at hdiv
    omega
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    rw [hkzero] at hlower
    simp only [zero_mul] at hlower
    omega
  exact ⟨hk, hlower, hupper, Nat.div_le_of_le_mul hlower⟩

private theorem inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_den_pos {d j : ℕ}
    (hd : 0 < d) (hj : 24 * d ≤ j) : 0 < d * j := by
  have hjpos : 0 < j := by omega
  exact Nat.mul_pos hd hjpos

 
theorem intrinsicPartitionBlockSize_pos {d j N : ℕ}
    (hd : 0 < d) (hj : 24 * d ≤ j) (hN : j * d < N) :
    0 < intrinsicPartitionBlockSize d j N := by
  exact (inline_Esgk_IntrinsicPartitionScale__intrinsicCeilingQuotient_bounds (inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_den_pos hd hj)
    (by simpa only [Nat.mul_comm] using hN)).1

 
theorem intrinsicPartitionBlockSize_cut_bound {d j N : ℕ}
    (hd : 0 < d) (hj : 24 * d ≤ j) (hN : j * d < N) :
    N / intrinsicPartitionBlockSize d j N ≤ d * j := by
  exact (inline_Esgk_IntrinsicPartitionScale__intrinsicCeilingQuotient_bounds (inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_den_pos hd hj)
    (by simpa only [Nat.mul_comm] using hN)).2.2.2

 
theorem intrinsicPartitionBlockSize_real_le {d j N : ℕ}
    (hd : 0 < d) (hj : 24 * d ≤ j) (hN : j * d < N) :
    (intrinsicPartitionBlockSize d j N : ℝ) ≤
      2 * (N : ℝ) / ((d : ℝ) * (j : ℝ)) := by
  have hq := inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_den_pos hd hj
  have hupper := (inline_Esgk_IntrinsicPartitionScale__intrinsicCeilingQuotient_bounds hq
    (by simpa only [Nat.mul_comm] using hN)).2.2.1
  have hden : 0 < (d : ℝ) * (j : ℝ) := by exact_mod_cast hq
  apply (le_div_iff₀ hden).mpr
  exact_mod_cast hupper

 
theorem intrinsicPartitionBlockSize_sq_le {d j N : ℕ}
    (hd : 0 < d) (hj : 24 * d ≤ j) (hN : j * d < N) :
    (intrinsicPartitionBlockSize d j N : ℝ) ^ 2 ≤
      4 * (N : ℝ) ^ 2 / ((d : ℝ) ^ 2 * (j : ℝ) ^ 2) := by
  have hq := inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_den_pos hd hj
  have hden : 0 < (d : ℝ) * (j : ℝ) := by exact_mod_cast hq
  have hupper := (le_div_iff₀ hden).mp (intrinsicPartitionBlockSize_real_le hd hj hN)
  have hnonneg : 0 ≤ (intrinsicPartitionBlockSize d j N : ℝ) *
      ((d : ℝ) * (j : ℝ)) := by positivity
  have hsquare := mul_self_le_mul_self hnonneg hupper
  have hdenSq : 0 < (d : ℝ) ^ 2 * (j : ℝ) ^ 2 := by
    nlinarith [sq_pos_of_pos hden]
  apply (le_div_iff₀ hdenSq).mpr
  nlinarith [hsquare]

private theorem inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_four_mul_arcs_le {d j cut arcs : ℕ}
    (hj : 24 * d ≤ j) (hcut : cut ≤ d * j)
    (harcs : arcs ≤ cut + 6 * d ^ 2) : 4 * arcs ≤ 5 * d * j := by
  have hscale := Nat.mul_le_mul_left d hj
  nlinarith


theorem intrinsicPartition_cell_count_le {d j cut arcs : ℕ}
    (hj : 24 * d ≤ j) (hcut : cut ≤ d * j)
    (harcs : arcs ≤ cut + 6 * d ^ 2) : arcs ^ 2 ≤ 2 * d ^ 2 * j ^ 2 := by
  have hfour := inline_Esgk_IntrinsicPartitionScale__intrinsicPartition_four_mul_arcs_le hj hcut harcs
  have hsquare := Nat.mul_le_mul hfour hfour
  nlinarith [Nat.zero_le (d ^ 2 * j ^ 2)]


theorem intrinsicPartition_visit_count_le {d j cut : ℕ}
    (hj : 24 * d ≤ j) (hcut : cut ≤ d * j) :
    4 * (2 * d * (2 * (cut + 3 * d * d) + 2 * d * d)) ≤ 20 * d * d * j := by
  have hcutScaled := Nat.mul_le_mul_left (16 * d) hcut
  have hscale := Nat.mul_le_mul_left (4 * d * d) hj
  nlinarith [Nat.zero_le (d * d * d)]

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna.
-/


noncomputable section

open Set Topology Filter

namespace Esgk


theorem isLocalHomeomorph_of_inverse_germs
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f)
    (hγ : ∀ x : X, ∃ γ : Y → X, γ (f x) = x ∧
      ∃ U : Set Y, IsOpen U ∧ f x ∈ U ∧ ContinuousOn γ U ∧
        (∀ᶠ y in 𝓝 (f x), f (γ y) = y) ∧
        (∀ᶠ z in 𝓝 x, γ (f z) = z)) :
    IsLocalHomeomorph f := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro x _
  obtain ⟨γ, hγx, U, hU, hfxU, hγU, hright, hleft⟩ := hγ x
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hleft
  obtain ⟨R, hRsub, hR, hfxR⟩ := mem_nhds_iff.mp hright
  have hγ_at : ContinuousAt γ (f x) := hγU.continuousAt (hU.mem_nhds hfxU)
  have hW_nhds : W ∈ 𝓝 (γ (f x)) := by
    rw [hγx]
    exact hW.mem_nhds hxW
  obtain ⟨V₀, hV₀sub, hV₀, hfxV₀⟩ :=
    mem_nhds_iff.mp (hγ_at.preimage_mem_nhds hW_nhds)
  let V : Set Y := U ∩ (R ∩ V₀)
  have hV : IsOpen V := hU.inter (hR.inter hV₀)
  have hfxV : f x ∈ V := ⟨hfxU, hfxR, hfxV₀⟩
  have hγV : ∀ ⦃y : Y⦄, y ∈ V → γ y ∈ W := by
    intro y hy
    exact hV₀sub hy.2.2
  have hrightV : ∀ ⦃y : Y⦄, y ∈ V → f (γ y) = y := by
    intro y hy
    exact hRsub hy.2.1
  let S : Set X := W ∩ f ⁻¹' V
  have hS : IsOpen S := hW.inter (hV.preimage hf)
  have hxS : x ∈ S := ⟨hxW, hfxV⟩
  have hγS : ∀ ⦃y : Y⦄, y ∈ V → γ y ∈ S := by
    intro y hy
    refine ⟨hγV hy, ?_⟩
    change f (γ y) ∈ V
    rw [show f (γ y) = y from hrightV hy]
    exact hy
  have hleftS : ∀ ⦃z : X⦄, z ∈ S → γ (f z) = z := by
    intro z hz
    exact hWsub hz.1
  have hopenMap : IsOpenMap (S.domRestrict f) := by
    intro O hO
    have hO' : IsOpen (Subtype.val '' O) := hS.isOpenMap_subtype_val O hO
    have hopen : IsOpen (V ∩ γ ⁻¹' (Subtype.val '' O)) :=
      (hγU.mono (by intro y hy; exact hy.1)).isOpen_inter_preimage
        hV hO'
    rw [show (S.domRestrict f) '' O = V ∩ γ ⁻¹' (Subtype.val '' O) by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨z.property.2, ?_⟩
        exact ⟨z, hz, (hleftS z.property).symm⟩
      · intro hy
        obtain ⟨z, hz, hzy⟩ := hy.2
        let q : S := ⟨γ y, hγS hy.1⟩
        have hqz : q = z := Subtype.ext hzy.symm
        refine ⟨q, ?_, ?_⟩
        · rw [hqz]
          exact hz
        · simpa [q] using hrightV hy.1]
    exact hopen
  let e : PartialEquiv X Y :=
    { toFun := f
      invFun := γ
      source := S
      target := V
      map_source' := fun _ hz ↦ hz.2
      map_target' := fun _ hy ↦ hγS hy
      left_inv' := fun _ hz ↦ hleftS hz
      right_inv' := fun _ hy ↦ hrightV hy }
  have hecont : ContinuousOn e e.source := by
    simpa [e] using hf.continuousOn.mono (subset_univ S)
  have heopen : IsOpenMap (e.source.domRestrict e) := by
    simpa [e] using hopenMap
  let eo : OpenPartialHomeomorph X Y :=
    OpenPartialHomeomorph.ofContinuousOpenRestrict e hecont heopen hS
  refine ⟨eo, ?_, ?_⟩
  · simpa [eo, e] using hxS
  · rfl

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk


theorem eval_eq_eval_specializeRemainingVariables {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ) :
    MvPolynomial.eval z p =
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
  have hcons : Fin.cons (z 0) (fun i : Fin n ↦ z i.succ) = z := by
    funext i
    exact Fin.cases (by simp) (fun j ↦ by simp) i
  calc
    MvPolynomial.eval z p =
        MvPolynomial.eval (Fin.cons (z 0) (fun i : Fin n ↦ z i.succ)) p := by rw [hcons]
    _ = Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) := by
      simpa [specializeRemainingVariables, headCurry] using
        (MvPolynomial.eval_eq_eval_mv_eval'
          (s := fun i : Fin n ↦ z i.succ) (y := z 0) p)

 
theorem resultant_specializeRemainingVariables {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (x : Fin n → ℝ) :
    Polynomial.resultant (specializeRemainingVariables x p) (specializeRemainingVariables x q)
        (headCurry p).natDegree (headCurry q).natDegree =
      MvPolynomial.eval x (headResultant p q) := by
  rw [specializeRemainingVariables, headResultant]
  exact Polynomial.resultant_map_map (headCurry p) (headCurry q)
    (headCurry p).natDegree (headCurry q).natDegree (MvPolynomial.eval x)

 
theorem eval_headResultant_eq_zero_of_common_zero {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (z : Fin (n + 1) → ℝ)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hp : MvPolynomial.eval z p = 0) (hq : MvPolynomial.eval z q = 0) :
    MvPolynomial.eval (fun i ↦ z i.succ) (headResultant p q) = 0 := by
  have hpSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) p) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hp
  have hqSpecialized :
      Polynomial.eval (z 0) (specializeRemainingVariables (fun i ↦ z i.succ) q) = 0 := by
    rw [← eval_eq_eval_specializeRemainingVariables]
    exact hq
  have hpDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) p).natDegree ≤
        (headCurry p).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry p))
  have hqDegreeLe :
      (specializeRemainingVariables (fun i ↦ z i.succ) q).natDegree ≤
        (headCurry q).natDegree := by
    simpa [specializeRemainingVariables] using
      (Polynomial.natDegree_map_le
        (f := MvPolynomial.eval (fun i ↦ z i.succ)) (p := headCurry q))
  obtain ⟨u, v, _, _, hbezout⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := specializeRemainingVariables (fun i ↦ z i.succ) p)
      (g := specializeRemainingVariables (fun i ↦ z i.succ) q)
      hpDegreeLe hqDegreeLe (Or.inl (Nat.ne_of_gt hpDegree))
  have hresultant :
      Polynomial.resultant
          (specializeRemainingVariables (fun i ↦ z i.succ) p)
          (specializeRemainingVariables (fun i ↦ z i.succ) q)
          (headCurry p).natDegree (headCurry q).natDegree = 0 := by
    have hzero :
        Polynomial.eval (z 0)
            (Polynomial.C
              (Polynomial.resultant
                (specializeRemainingVariables (fun i ↦ z i.succ) p)
                (specializeRemainingVariables (fun i ↦ z i.succ) q)
                (headCurry p).natDegree (headCurry q).natDegree)) = 0 := by
      rw [← hbezout]
      simp [hpSpecialized, hqSpecialized]
    simpa using hzero
  rw [← resultant_specializeRemainingVariables]
  exact hresultant

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology

namespace Esgk

variable {X : Type*} [TopologicalSpace X]

private theorem inline_Esgk_OpenConnectedPartition__open_preconnected_family_component_eq_aux
    (A : Set (Set X))
    (hopen : ∀ C ∈ A, IsOpen C)
    (hpre : ∀ C ∈ A, IsPreconnected C)
    (hdisj : ∀ {C D : Set X}, C ∈ A → D ∈ A → C ≠ D → Disjoint C D)
    {C : Set X} (hC : C ∈ A) {x : X} (hx : x ∈ C) :
    C = connectedComponentIn (⋃₀ A) x := by
  let U : Set X := ⋃₀ A
  have hCsub : C ⊆ U := subset_sUnion_of_mem hC
  have hCcomp : C ⊆ connectedComponentIn U x :=
    (hpre C hC).subset_connectedComponentIn hx hCsub
  let Aother : Set (Set X) := {D | D ∈ A ∧ D ≠ C}
  have hAotheropen : IsOpen (⋃₀ Aother) :=
    isOpen_sUnion fun D hD ↦ hopen D hD.1
  have hUdiff : U \ C = ⋃₀ Aother := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨D, hD, hyD⟩ := mem_sUnion.mp hy.1
      by_cases hDC : D = C
      · exact False.elim (hy.2 (hDC ▸ hyD))
      · exact mem_sUnion_of_mem hyD ⟨hD, hDC⟩
    · intro y hy
      obtain ⟨D, hD, hyD⟩ := mem_sUnion.mp hy
      refine ⟨subset_sUnion_of_mem hD.1 hyD, ?_⟩
      intro hyC
      exact Set.disjoint_left.mp (hdisj hC hD.1 (Ne.symm hD.2)) hyC hyD
  have hotheropen : IsOpen (U \ C) := by
    rw [hUdiff]
    exact hAotheropen
  have hcompC : connectedComponentIn U x ⊆ C := by
    have hcompPre : IsPreconnected (connectedComponentIn U x) :=
      isPreconnected_connectedComponentIn
    have hcover : connectedComponentIn U x ⊆ C ∪ (U \ C) := by
      intro y hy
      have hyU : y ∈ U := connectedComponentIn_subset U x hy
      by_cases hyC : y ∈ C
      · exact Or.inl hyC
      · exact Or.inr ⟨hyU, hyC⟩
    have hdisjoint : Disjoint C (U \ C) := by
      apply Set.disjoint_left.mpr
      intro y hyC hyother
      exact hyother.2 hyC
    rcases hcompPre.subset_or_subset (hopen C hC) hotheropen
      hdisjoint hcover with h | h
    · exact h
    · have hxcomp : x ∈ connectedComponentIn U x :=
        mem_connectedComponentIn (hCsub hx)
      exact False.elim ((h hxcomp).2 hx)
  exact hCcomp.antisymm hcompC


theorem open_preconnected_family_component_eq
    (A : Set (Set X))
    (hopen : ∀ C ∈ A, IsOpen C)
    (hpre : ∀ C ∈ A, IsPreconnected C)
    (hdisj : ∀ {C D : Set X}, C ∈ A → D ∈ A → C ≠ D → Disjoint C D)
    {C : Set X} (hC : C ∈ A) {x : X} (hx : x ∈ C) :
    C = connectedComponentIn (⋃₀ A) x :=
  inline_Esgk_OpenConnectedPartition__open_preconnected_family_component_eq_aux A hopen hpre hdisj hC hx


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : Polynomial K) (hq : 0 < q.natDegree) :
    0 < q.roots.toFinset.card := by
  have hroots_card : q.roots.card = q.natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hroots_ne : q.roots ≠ 0 := by
    intro hzero
    rw [hzero] at hroots_card
    simp at hroots_card
    omega
  exact Finset.card_pos.mpr (Multiset.toFinset_nonempty.mpr hroots_ne)


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open _root_.Polynomial


theorem Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
    (p : ℂ[X]) (_hp : p ≠ 0) {τ : ℂ} (hτ : p.roots.toFinset = {τ}) :
    p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  have hroots : p.roots = Multiset.replicate p.roots.card τ := by
    apply Multiset.eq_replicate_card.mpr
    intro z hz
    have hz' : z ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr hz
    simpa [hτ] using hz'
  calc
    p = C p.leadingCoeff * (p.roots.map (X - C ·)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
      rw [hroots, Multiset.map_replicate, Multiset.prod_replicate,
        IsAlgClosed.card_roots_eq_natDegree]


theorem Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
    (p : ℂ[X]) (_hp : p ≠ 0) (hcard : p.roots.toFinset.card = 1) :
    ∃ τ : ℂ, p = C p.leadingCoeff * (X - C τ) ^ p.natDegree := by
  classical
  obtain ⟨τ, hτ⟩ := Finset.card_eq_one.mp hcard
  exact ⟨τ,
    Polynomial.eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_eq_singleton
      p _hp hτ⟩

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology

namespace Esgk

 
theorem injOn_of_real_chart
    {X : Type*} [TopologicalSpace X] {C : Set X} {J : Set ℝ}
    (e : C ≃ₜ J) (f : X → ℝ) (he : ∀ p : C, (e p : ℝ) = f p) :
    Set.InjOn f C := by
  intro p hp q hq hpq
  have heq : e ⟨p, hp⟩ = e ⟨q, hq⟩ := by
    apply Subtype.ext
    simpa only [he] using hpq
  exact congrArg Subtype.val (e.injective heq)

 
theorem isConnected_real_chart_slice
    {X : Type*} [TopologicalSpace X] {C : Set X} {J V : Set ℝ}
    (e : C ≃ₜ J) (f : X → ℝ) (he : ∀ p : C, (e p : ℝ) = f p)
    (hVJ : V ⊆ J) (hV : IsConnected V) :
    IsConnected (C ∩ f ⁻¹' V) := by
  let W : Set J := Subtype.val ⁻¹' V
  have himage : (Subtype.val : J → ℝ) '' W = V := by
    ext t
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro ht
      exact ⟨⟨t, hVJ ht⟩, ht, rfl⟩
  have hW : IsConnected W := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨t, ht⟩ := hV.nonempty
      exact ⟨⟨t, hVJ ht⟩, ht⟩
    · rw [himage]
      exact hV.isPreconnected
  let g : J → X := fun t ↦ (e.symm t : X)
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgimage : g '' W = C ∩ f ⁻¹' V := by
    ext p
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(e.symm t).property, ?_⟩
      have hcoord : f (e.symm t) = (t : ℝ) := by
        rw [← he]
        simp
      change f (e.symm t) ∈ V
      rwa [hcoord]
    · rintro ⟨hpC, hpV⟩
      refine ⟨e ⟨p, hpC⟩, ?_, ?_⟩
      · change (e ⟨p, hpC⟩ : ℝ) ∈ V
        rwa [he]
      · change ((e.symm (e ⟨p, hpC⟩) : C) : X) = p
        simp
  rw [← hgimage]
  exact hW.image g hg.continuousOn


theorem isOpen_real_chart_slice
    {X : Type*} [TopologicalSpace X] {C : Set X} {V : Set ℝ}
    (hC : IsOpen C) {f : X → ℝ} (hf : Continuous f) (hV : IsOpen V) :
    IsOpen (C ∩ f ⁻¹' V) :=
  hC.inter (hV.preimage hf)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk


theorem twoAnchor_sqDistance_eq_same_or_reflection
    {a x₁ y₁ x₂ y₂ : ℝ}
    (ha : 0 < a)
    (h₁ : (x₁ + a) ^ 2 + y₁ ^ 2 = (x₂ + a) ^ 2 + y₂ ^ 2)
    (h₂ : (x₁ - a) ^ 2 + y₁ ^ 2 = (x₂ - a) ^ 2 + y₂ ^ 2) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = x₂ ∧ y₁ = -y₂) := by
  have hx : x₁ = x₂ := by
    nlinarith [h₁, h₂]
  have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
    nlinarith [h₁, hx]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy_sq with hy | hy
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩














end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


@[simp]
theorem bivariateCornerExponent_zero (p : ℕ) : bivariateCornerExponent p 0 = p := by
  simp [bivariateCornerExponent]

@[simp]
theorem bivariateCornerExponent_one (p : ℕ) : bivariateCornerExponent p 1 = p := by
  simp [bivariateCornerExponent]


theorem coeff_bivariateCornerRemainder (p : ℕ) (Q : BidegreePolynomial ℂ)
    (e : Fin 2 →₀ ℕ) :
    coeff e (bivariateCornerRemainder p Q) =
      if e = bivariateCornerExponent p then 0 else coeff e Q := by
  rw [bivariateCornerRemainder, coeff_sub, coeff_monomial]
  by_cases he : e = bivariateCornerExponent p
  · subst e
    simp
  · simp [he, Ne.symm he]

@[simp]
theorem coeff_bivariateCornerRemainder_corner (p : ℕ) (Q : BidegreePolynomial ℂ) :
    coeff (bivariateCornerExponent p) (bivariateCornerRemainder p Q) = 0 := by
  simp [coeff_bivariateCornerRemainder]

 
theorem coeff_bivariateCornerExponent_ne_zero (Q : BidegreePolynomial ℂ) (p : ℕ)
    (hp : 0 < p) (hbound : BidegreeBound p Q) (htotal : Q.totalDegree = 2 * p) :
    coeff (bivariateCornerExponent p) Q ≠ 0 := by
  have hQ : Q ≠ 0 := by
    intro hzero
    subst Q
    simp at htotal
    omega
  obtain ⟨e, he, hmax⟩ :=
    Finset.exists_mem_eq_sup Q.support (MvPolynomial.support_nonempty.mpr hQ)
      (fun e ↦ e.sum fun _ k ↦ k)
  have hesum : e.sum (fun _ k ↦ k) = 2 * p := by
    calc
      e.sum (fun _ k ↦ k) = Q.support.sup (fun e ↦ e.sum fun _ k ↦ k) := hmax.symm
      _ = Q.totalDegree := rfl
      _ = 2 * p := htotal
  have hesum' : e 0 + e 1 = 2 * p := by
    simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hesum
  have hezero : e 0 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have heone : e 1 = p := by
    have := (hbound e he).1
    have := (hbound e he).2
    omega
  have hecorner : e = bivariateCornerExponent p := by
    apply Finsupp.ext
    intro i
    fin_cases i
    · simpa using hezero
    · simpa using heone
  rw [← hecorner]
  exact MvPolynomial.mem_support_iff.mp he


theorem mem_support_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0)
    {e : Fin 2 →₀ ℕ} (he : e ∈ (bivariateCornerRemainder p Q).support) :
    e ∈ Q.support ∧ e 0 < p ∧ e 1 < p := by
  have hcoeffR : coeff e (bivariateCornerRemainder p Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp he
  have hne : e ≠ bivariateCornerExponent p := by
    intro hecorner
    subst e
    exact hcoeffR (coeff_bivariateCornerRemainder_corner p Q)
  have hcoeffQ : coeff e Q ≠ 0 := by
    rw [coeff_bivariateCornerRemainder, if_neg hne] at hcoeffR
    exact hcoeffR
  have heQ : e ∈ Q.support := MvPolynomial.mem_support_iff.mpr hcoeffQ
  have hezero_le := (hbound e heQ).1
  have heone_le := (hbound e heQ).2
  have hezero_lt : e 0 < p := by
    by_contra hnot
    have hezero : e 0 = p := by omega
    by_cases heone : e 1 = p
    · apply hne
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simpa using heone
    · have heone_lt : e 1 < p := by omega
      have hzero := hcolumn (e 1) heone_lt
      apply hcoeffQ
      rw [← hzero]
      congr 1
      apply Finsupp.ext
      intro i
      fin_cases i
      · simpa using hezero
      · simp
  have heone_lt : e 1 < p := by
    by_contra hnot
    have heone : e 1 = p := by omega
    have hzero := hrow (e 0) hezero_lt
    apply hcoeffQ
    rw [← hzero]
    congr 1
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp
    · simpa using heone
  exact ⟨heQ, hezero_lt, heone_lt⟩

 
theorem bidegreeBound_bivariateCornerRemainder
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    BidegreeBound (p - 1) (bivariateCornerRemainder p Q) := by
  intro e he
  obtain ⟨_, hezero, heone⟩ :=
    mem_support_bivariateCornerRemainder Q p hbound hrow hcolumn he
  constructor <;> omega


theorem exists_bivariate_corner_normal_form
    (Q : BidegreePolynomial ℂ) (p : ℕ) (hp : 0 < p) (hbound : BidegreeBound p Q)
    (htotal : Q.totalDegree = 2 * p)
    (hrow : ∀ a < p,
      coeff (Finsupp.single 0 a + Finsupp.single 1 p) Q = 0)
    (hcolumn : ∀ b < p,
      coeff (Finsupp.single 0 p + Finsupp.single 1 b) Q = 0) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧ Q = monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  refine ⟨coeff (bivariateCornerExponent p) Q, bivariateCornerRemainder p Q,
    coeff_bivariateCornerExponent_ne_zero Q p hp hbound htotal, ?_,
    bidegreeBound_bivariateCornerRemainder Q p hp hbound hrow hcolumn⟩
  rw [bivariateCornerRemainder]
  abel

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise Real InnerProductSpace EuclideanSpace

variable {n : ℕ}


local notation "o" => (positiveOrientation : Orientation ℝ _root_.Point2 (Fin 2))

 
local notation "J" => Orientation.rightAngleRotation o


lemma directLinearIsometryEquivOfSend_apply_u (u v : _root_.Point2) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    directLinearIsometryEquivOfSend u v hu huv u = v := by
  have hv : v ≠ 0 := bundle_Esgk_BridgeIdentity_ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ _root_.Point2 := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ _root_.Point2 := o.basisRightAngleRotation v hv with hbv_def
   
  change (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) u = v
  have h0u : bᵤ 0 = u := by rw [hbu_def, o.coe_basisRightAngleRotation u hu]; rfl
  have h0v : bᵥ 0 = v := by rw [hbv_def, o.coe_basisRightAngleRotation v hv]; rfl
   
  have happ : (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) (bᵤ 0) = bᵥ 0 := by
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
   
  rw [← h0u, happ, h0v]


lemma directAffineIsometryEquivOfSendPair_apply_a (a b c d : _root_.Point2) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist a = c := by
  unfold directAffineIsometryEquivOfSendPair
  simp

 
lemma directAffineIsometryEquivOfSendPair_apply_b (a b c d : _root_.Point2) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist b = d := by
  unfold directAffineIsometryEquivOfSendPair
  change directLinearIsometryEquivOfSend (b - a) (d - c) _ _ (b - a) + c = d
  rw [directLinearIsometryEquivOfSend_apply_u]
  abel


end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

private theorem inline_Esgk_FiniteIncidenceCoverBound__finiteIncidenceCount_le_card_mul_pointFiber
    {α β : Type*} (bad : Finset α) (C : Finset β)
    (R : α → β → Prop) (B : ℕ)
    (hfiber : ∀ p ∈ bad, (C.filter (fun c ↦ R p c)).card ≤ B) :
    finiteIncidenceCount bad C R ≤ bad.card * B := by
  classical
  simp only [finiteIncidenceCount, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ bad, ∑ c ∈ C, if R p c then 1 else 0) ≤
        ∑ p ∈ bad, B := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [Finset.card_filter] using hfiber p hp
    _ = bad.card * B := by simp


theorem finiteIncidenceCount_le_of_cover
    {α β ι : Type*}
    (P : Finset α) (C : Finset β) (R : α → β → Prop)
    (bad : Finset α) (cells : Finset ι)
    (Pω : ι → Finset α) (Cω : ι → Finset β) (B : ℕ)
    (hcover : ∀ p ∈ P, p ∈ bad ∨ ∃ ω ∈ cells, p ∈ Pω ω)
    (hlabels : ∀ ω ∈ cells, ∀ p ∈ Pω ω, ∀ c ∈ C, R p c → c ∈ Cω ω)
    (hfiber : ∀ p ∈ bad, (C.filter (fun c ↦ R p c)).card ≤ B) :
    finiteIncidenceCount P C R ≤
      bad.card * B + ∑ ω ∈ cells, finiteIncidenceCount (Pω ω) (Cω ω) R := by
  classical
  rw [finiteIncidenceCount_eq_card_filter_product]
  let Ibad : Finset (α × β) :=
    (bad.product C).filter (fun z ↦ R z.1 z.2)
  let Icell : ι → Finset (α × β) := fun ω ↦
    ((Pω ω).product (Cω ω)).filter (fun z ↦ R z.1 z.2)
  have hcoverSet :
      (P.product C).filter (fun z ↦ R z.1 z.2) ⊆
        Ibad ∪ cells.biUnion Icell := by
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzPC := Finset.mem_product.mp hz'.1
    rcases hcover z.1 hzPC.1 with hbad | ⟨ω, hω, hpω⟩
    · exact Finset.mem_union_left _ (by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨hbad, hzPC.2⟩, hz'.2⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨ω, hω, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨hpω, ?_⟩, hz'.2⟩
      exact hlabels ω hω z.1 hpω z.2 hzPC.2 hz'.2
  have hbadCard : Ibad.card ≤ bad.card * B := by
    change ((bad.product C).filter (fun z ↦ R z.1 z.2)).card ≤ bad.card * B
    calc
      ((bad.product C).filter (fun z ↦ R z.1 z.2)).card =
          finiteIncidenceCount bad C R :=
        (finiteIncidenceCount_eq_card_filter_product bad C R).symm
      _ ≤ bad.card * B :=
        inline_Esgk_FiniteIncidenceCoverBound__finiteIncidenceCount_le_card_mul_pointFiber bad C R B hfiber
  have hcellEq :
      (∑ ω ∈ cells, (Icell ω).card) =
        ∑ ω ∈ cells, finiteIncidenceCount (Pω ω) (Cω ω) R := by
    apply Finset.sum_congr rfl
    intro ω hω
    exact (finiteIncidenceCount_eq_card_filter_product
      (Pω ω) (Cω ω) R).symm
  calc
    ((P.product C).filter (fun z ↦ R z.1 z.2)).card ≤
        (Ibad ∪ cells.biUnion Icell).card := Finset.card_le_card hcoverSet
    _ ≤ Ibad.card + (cells.biUnion Icell).card := Finset.card_union_le _ _
    _ ≤ Ibad.card + ∑ ω ∈ cells, (Icell ω).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ bad.card * B + ∑ ω ∈ cells, (Icell ω).card := by
      exact Nat.add_le_add_right hbadCard _
    _ = bad.card * B + ∑ ω ∈ cells,
        finiteIncidenceCount (Pω ω) (Cω ω) R := by rw [hcellEq]

end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

namespace IrreduciblePlanePolynomial

variable {F : Type*} [Field F]


@[simp]
theorem coordinateRingAlgEquivTransport_apply_mk
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (p : MvPolynomial (Fin 2) F) :
    C.coordinateRingAlgEquivTransport e
        (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (e p) :=
  rfl


@[simp]
theorem functionFieldAlgEquivTransport_apply_algebraMap
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (a : C.CoordinateRing) :
    C.functionFieldAlgEquivTransport e
        (algebraMap C.CoordinateRing C.FunctionField a) =
      algebraMap (C.transportByAlgEquiv e).CoordinateRing
        (C.transportByAlgEquiv e).FunctionField
        (C.coordinateRingAlgEquivTransport e a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (C.coordinateRingAlgEquivTransport e) a

@[simp]
theorem functionFieldAlgEquivTransport_symm_apply_algebraMap
    (C : IrreduciblePlanePolynomial F)
    (e : MvPolynomial (Fin 2) F ≃ₐ[F] MvPolynomial (Fin 2) F)
    (a : (C.transportByAlgEquiv e).CoordinateRing) :
    (C.functionFieldAlgEquivTransport e).symm
        (algebraMap (C.transportByAlgEquiv e).CoordinateRing
          (C.transportByAlgEquiv e).FunctionField a) =
      algebraMap C.CoordinateRing C.FunctionField
        ((C.coordinateRingAlgEquivTransport e).symm a) := by
  exact IsFractionRing.algEquivOfAlgEquiv_algebraMap
    (C.coordinateRingAlgEquivTransport e).symm a


end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology

namespace Esgk

 
theorem locallyConnectedSpace_of_real_charts
    {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ e : OpenPartialHomeomorph X ℝ, x ∈ e.source) :
    LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_subsets_isOpen_isConnected]
  intro x U hU
  obtain ⟨e, hx⟩ := h x
  let : LocallyConnectedSpace e.source := e.isOpenEmbedding_restrict.locallyConnectedSpace
  let x' : e.source := ⟨x, hx⟩
  have hU' : (Subtype.val : e.source → X) ⁻¹' U ∈ 𝓝 x' :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, hVU, hV, hxV, hVc⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x' _ hU'
  refine ⟨Subtype.val '' V, ?_, e.open_source.isOpenMap_subtype_val V hV,
    ⟨x', hxV, rfl⟩, hVc.image Subtype.val continuous_subtype_val.continuousOn⟩
  rintro y ⟨v, hv, rfl⟩
  exact hVU hv


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open scoped BigOperators

namespace Esgk

lemma fin_sum_val_add (a b : ℕ) :
    (∑ i : Fin (a + b), (i : ℕ)) =
      (∑ i : Fin a, (i : ℕ)) + (∑ i : Fin b, (i : ℕ)) + a * b := by
  rw [Fin.sum_univ_add]
  simp_rw [Fin.val_castAdd, Fin.val_natAdd, Nat.add_comm a]
  rw [Finset.sum_add_distrib]
  simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm]

lemma sylvester_selected_index_sum {m n : ℕ} (σ : Fin (m + n) → Fin (m + n))
    (hσ : Function.Bijective σ)
    (hl : ∀ i : Fin m, i.val ≤ (σ (Fin.castAdd n i)).val ∧
      (σ (Fin.castAdd n i)).val ≤ i.val + n)
    (hr : ∀ j : Fin n, j.val ≤ (σ (Fin.natAdd m j)).val ∧
      (σ (Fin.natAdd m j)).val ≤ j.val + m) :
    (∑ i : Fin m, ((σ (Fin.castAdd n i)).val - i.val)) +
      (∑ j : Fin n, ((σ (Fin.natAdd m j)).val - j.val)) = m * n := by
  have hsigma : (∑ x : Fin (m + n), (σ x).val) = ∑ x : Fin (m + n), x.val := by
    let e : Fin (m + n) ≃ Fin (m + n) := Equiv.ofBijective σ hσ
    simpa [e] using (e.sum_comp (fun x : Fin (m + n) => x.val))
  have hleft := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin m)))
    (f := fun i : Fin m => (σ (Fin.castAdd n i)).val) (g := fun i => i.val)
    (fun i _ => (hl i).1)
  have hright := Finset.sum_tsub_distrib (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n => (σ (Fin.natAdd m j)).val) (g := fun j => j.val)
    (fun j _ => (hr j).1)
  rw [hleft, hright]
  have hAB : (∑ i : Fin m, i.val) ≤ ∑ i : Fin m, (σ (Fin.castAdd n i)).val :=
    Finset.sum_le_sum (fun i _ => (hl i).1)
  have hCD : (∑ j : Fin n, j.val) ≤ ∑ j : Fin n, (σ (Fin.natAdd m j)).val :=
    Finset.sum_le_sum (fun j _ => (hr j).1)
  have hcombine :
      (∑ i : Fin m, (σ (Fin.castAdd n i)).val) - ∑ i : Fin m, i.val +
        ((∑ j : Fin n, (σ (Fin.natAdd m j)).val) - ∑ j : Fin n, j.val) =
        ((∑ i : Fin m, (σ (Fin.castAdd n i)).val) +
          ∑ j : Fin n, (σ (Fin.natAdd m j)).val) -
        ((∑ i : Fin m, i.val) + ∑ j : Fin n, j.val) := by omega
  rw [hcombine]
  rw [← Fin.sum_univ_add (fun x : Fin (m + n) => (σ x).val)]
  rw [hsigma]
  rw [fin_sum_val_add]
  omega

lemma nat_sub_add_sub_le {a b c x y : ℕ} (hx : x ≤ a) (hy : y ≤ b) (hxy : x + y = c) :
    a - x + (b - y) ≤ a + b - c := by omega


theorem headResultant_totalDegree_le_weighted {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤
      (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
        (headCurry p).natDegree * (headCurry q).natDegree := by
  classical
  rw [headResultant, Polynomial.resultant, Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ hσ
  by_cases hterm : ∏ i : Fin ((headCurry p).natDegree + (headCurry q).natDegree),
      Polynomial.sylvester (headCurry p) (headCurry q)
        (headCurry p).natDegree (headCurry q).natDegree (σ i) i = 0
  · rw [hterm]
    change 0 ≤ _
    omega
  · apply (MvPolynomial.totalDegree_smul_le _ _).trans
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    rw [Fin.sum_univ_add]
    let m := (headCurry p).natDegree
    let k := (headCurry q).natDegree
    have hprod (i : Fin (m + k)) :
        Polynomial.sylvester (headCurry p) (headCurry q) m k (σ i) i ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i)
    have hl (i : Fin m) :
        i.val ≤ (σ (Fin.castAdd k i)).val ∧
          (σ (Fin.castAdd k i)).val ≤ i.val + k := by
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hr (j : Fin k) :
        j.val ≤ (σ (Fin.natAdd m j)).val ∧
          (σ (Fin.natAdd m j)).val ≤ j.val + m := by
      have hi := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hi
      split_ifs at hi with h
      · exact h
      · simp_all
    have hsel := sylvester_selected_index_sum σ σ.bijective hl hr
    have hleft : ∀ i : Fin m,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.castAdd k i)) (Fin.castAdd k i)).totalDegree ≤
          d₂ - ((σ (Fin.castAdd k i)).val - i.val) := by
      intro i
      have hi := hprod (Fin.castAdd k i)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi ⊢
      split_ifs with h
      · exact hq _
      · simp_all
    have hright : ∀ j : Fin k,
        (Polynomial.sylvester (headCurry p) (headCurry q) m k
          (σ (Fin.natAdd m j)) (Fin.natAdd m j)).totalDegree ≤
          d₁ - ((σ (Fin.natAdd m j)).val - j.val) := by
      intro j
      have hj := hprod (Fin.natAdd m j)
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj ⊢
      split_ifs with h
      · exact hp _
      · simp_all
    apply Nat.le_trans (Nat.add_le_add
      (Finset.sum_le_sum fun i _ => hleft i)
      (Finset.sum_le_sum fun j _ => hright j))
    have hqidx : ∀ i : Fin m, (σ (Fin.castAdd k i)).val - i.val ≤ d₂ := by
      intro i
      have hc : (headCurry q).coeff ((σ (Fin.castAdd k i)).val - i.val) ≠ 0 := by
        have hi := hprod (Fin.castAdd k i)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left] at hi
        split_ifs at hi with h
        · exact hi
        · simp at hi
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hqHead
    have hpidx : ∀ j : Fin k, (σ (Fin.natAdd m j)).val - j.val ≤ d₁ := by
      intro j
      have hc : (headCurry p).coeff ((σ (Fin.natAdd m j)).val - j.val) ≠ 0 := by
        have hj := hprod (Fin.natAdd m j)
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right] at hj
        split_ifs at hj with h
        · exact hj
        · simp at hj
      exact (Polynomial.le_natDegree_of_ne_zero hc).trans hpHead
    rw [Finset.sum_tsub_distrib _ (fun i _ => hqidx i)]
    rw [Finset.sum_tsub_distrib _ (fun j _ => hpidx j)]
    have hc : (∑ _ : Fin m, d₂) = m * d₂ := by simp
    have hc' : (∑ _ : Fin k, d₁) = k * d₁ := by simp
    rw [hc, hc']
    have hQ : (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ m * d₂ := by
      calc
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) ≤ ∑ _ : Fin m, d₂ :=
          Finset.sum_le_sum fun i _ => hqidx i
        _ = m * d₂ := hc
    have hP : (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ k * d₁ := by
      calc
        (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) ≤ ∑ _ : Fin k, d₁ :=
          Finset.sum_le_sum fun j _ => hpidx j
        _ = k * d₁ := hc'
    have hsel' :
        (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
            (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k := by
      change (∑ i : Fin m, ((σ (Fin.castAdd k i)).val - (i : ℕ))) +
          (∑ j : Fin k, ((σ (Fin.natAdd m j)).val - (j : ℕ))) = m * k at hsel
      exact hsel
    rw [Nat.add_comm ((headCurry q).natDegree * d₁) ((headCurry p).natDegree * d₂)]
    exact nat_sub_add_sub_le hQ hP hsel'

theorem headResultant_totalDegree_le_weighted_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) (d₁ d₂ : ℕ)
    (hpHead : (headCurry p).natDegree ≤ d₁)
    (hqHead : (headCurry q).natDegree ≤ d₂)
    (hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ d₁ - k)
    (hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ d₂ - k) :
    (headResultant p q).totalDegree ≤ d₁ * d₂ := by
  apply (headResultant_totalDegree_le_weighted p q d₁ d₂ hpHead hqHead hp hq).trans
  let m := (headCurry p).natDegree
  let k := (headCurry q).natDegree
  have hmk : m * k ≤ k * d₁ := by
    simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_left k hpHead
  have hsplit : k * d₁ + m * d₂ - m * k = m * d₂ + (k * d₁ - m * k) := by
    rw [Nat.add_comm (k * d₁) (m * d₂), Nat.add_sub_assoc hmk]
  have hdiff : k * d₁ - m * k ≤ d₂ * (d₁ - m) := by
    calc
      k * d₁ - m * k = (d₁ - m) * k := by
        rw [Nat.mul_sub_right_distrib]
        ac_rfl
      _ ≤ d₂ * (d₁ - m) := by
        simpa [m, k, Nat.mul_comm] using Nat.mul_le_mul_right (d₁ - m) hqHead
  have hsplit_le : m * d₂ + (k * d₁ - m * k) ≤ d₁ * d₂ := by
    calc
      m * d₂ + (k * d₁ - m * k) ≤ m * d₂ + d₂ * (d₁ - m) :=
        Nat.add_le_add_left hdiff _
      _ = d₁ * d₂ := by
        have hd : m + (d₁ - m) = d₁ := Nat.add_sub_of_le hpHead
        rw [show m * d₂ = d₂ * m by ac_rfl]
        rw [← Nat.mul_add, hd]
        ac_rfl
  rw [show (headCurry q).natDegree * d₁ + (headCurry p).natDegree * d₂ -
      (headCurry p).natDegree * (headCurry q).natDegree =
      m * d₂ + (k * d₁ - m * k) by simpa [m, k] using hsplit]
  exact hsplit_le

theorem headResultant_totalDegree_le_totalDegree_mul {n : ℕ}
    (p q : MvPolynomial (Fin (n + 1)) ℝ) :
    (headResultant p q).totalDegree ≤ p.totalDegree * q.totalDegree := by
  have hpHead : (headCurry p).natDegree ≤ p.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n p).natDegree ≤ p.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree p 0
  have hqHead : (headCurry q).natDegree ≤ q.totalDegree := by
    change (MvPolynomial.finSuccEquiv ℝ n q).natDegree ≤ q.totalDegree
    rw [MvPolynomial.natDegree_finSuccEquiv]
    exact MvPolynomial.degreeOf_le_totalDegree q 0
  have hp : ∀ k, ((headCurry p).coeff k).totalDegree ≤ p.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n p).coeff k).totalDegree ≤ p.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n p).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le p k hk
      omega
  have hq : ∀ k, ((headCurry q).coeff k).totalDegree ≤ q.totalDegree - k := by
    intro k
    change ((MvPolynomial.finSuccEquiv ℝ n q).coeff k).totalDegree ≤ q.totalDegree - k
    by_cases hk : (MvPolynomial.finSuccEquiv ℝ n q).coeff k = 0
    · simp [hk]
    · have hdegree := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le q k hk
      omega
  exact headResultant_totalDegree_le_weighted_mul p q p.totalDegree q.totalDegree
    hpHead hqHead hp hq

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open scoped Classical

namespace Esgk

variable {M : Type*} [TopologicalSpace M]


theorem frontier_subset_frontier_sUnion_of_open_pairwise_disjoint
    (A : Set (Set M))
    (hopen : ∀ C ∈ A, IsOpen C)
    (hdisj : ∀ {C D : Set M}, C ∈ A → D ∈ A → C ≠ D → Disjoint C D)
    {C : Set M} (hC : C ∈ A) :
    frontier C ⊆ frontier (⋃₀ A) := by
  intro p hp
  rw [frontier] at hp ⊢
  refine ⟨closure_mono (subset_sUnion_of_mem hC) hp.1, ?_⟩
  intro hpU
  obtain ⟨D, hD, hpD⟩ := mem_sUnion.mp (interior_subset hpU)
  have hDC : D = C := by
    by_contra hne
    obtain ⟨q, hqD, hqC⟩ := mem_closure_iff.mp hp.1 D (hopen D hD) hpD
    exact Set.disjoint_left.mp (hdisj hC hD (Ne.symm hne)) hqC hqD
  apply hp.2
  rw [← hDC]
  exact mem_interior_iff_mem_nhds.mpr ((hopen D hD).mem_nhds hpD)


theorem Finset.card_filter_closure_le_two_of_open_preconnected_pairwise_disjoint
    [T1Space M] [LocallyConnectedSpace M]
    (A : Finset (Set M))
    (hA_nonempty : ∀ C ∈ A, C.Nonempty)
    (hAopen : ∀ C ∈ A, IsOpen C)
    (hApre : ∀ C ∈ A, IsPreconnected C)
    (hApair : (A : Set (Set M)).Pairwise Disjoint)
    (B : Finset M) (hfrontier : frontier (⋃ C ∈ A, C) ⊆ (B : Set M))
    {p : M} (e : OpenPartialHomeomorph M ℝ) (hp : p ∈ e.source) :
    (A.filter (fun C ↦ p ∈ closure C)).card ≤ 2 := by
  let U : Set M := ⋃₀ (A : Set (Set M))
  have hUeq : U = ⋃ C ∈ A, C := by
    ext q
    simp [U]
  have hUopen : IsOpen U := by
    dsimp [U]
    exact isOpen_sUnion (fun C hC ↦ hAopen C hC)
  have hdisj : ∀ {C D : Set M}, C ∈ (A : Set (Set M)) →
      D ∈ (A : Set (Set M)) → C ≠ D → Disjoint C D := by
    intro C D hC hD hne
    exact hApair hC hD hne
  let F : Finset (Set M) := A.filter (fun C ↦ p ∈ closure C)
  let g : F → Set M := fun C ↦
    connectedComponentIn U
      (Classical.choose (hA_nonempty C.1 (Finset.mem_filter.mp C.2).1))
  have hchoose_mem (C : F) :
      Classical.choose (hA_nonempty C.1 (Finset.mem_filter.mp C.2).1) ∈ C.1 :=
    Classical.choose_spec (hA_nonempty C.1 (Finset.mem_filter.mp C.2).1)
  have hcomp_eq (C : F) : C.1 = g C := by
    exact open_preconnected_family_component_eq
      (A := (A : Set (Set M)))
      (fun D hD ↦ hAopen D hD)
      (fun D hD ↦ hApre D hD)
      hdisj (Finset.mem_filter.mp C.2).1 (hchoose_mem C)
  have hg_inj : Function.Injective g := by
    intro C D hCD
    apply Subtype.ext
    exact (hcomp_eq C).trans (hCD.trans (hcomp_eq D).symm)
  let G : Finset (Set M) := F.attach.image g
  have hGcard : G.card = F.card := by
    dsimp [G]
    rw [Finset.card_image_of_injective _ hg_inj, Finset.card_attach]
  have hGsubset : (G : Set (Set M)) ⊆
      {C : Set M | ∃ x ∈ U, C = connectedComponentIn U x ∧ p ∈ closure C} := by
    intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    have hDF := Finset.mem_filter.mp D.2
    have hclosure : p ∈ closure (g D) := by
      rw [← hcomp_eq D]
      exact hDF.2
    refine ⟨Classical.choose (hA_nonempty D.1 hDF.1), ?_, rfl, hclosure⟩
    exact subset_sUnion_of_mem hDF.1 (hchoose_mem D)
  have hbound := connectedComponentIn_closure_finite_and_ncard_le_two
    U B hUopen (by rw [hUeq]; exact hfrontier) e hp
  calc
    (A.filter (fun C ↦ p ∈ closure C)).card = F.card := by rfl
    _ = G.card := hGcard.symm
    _ = (G : Set (Set M)).ncard := (Set.ncard_coe_finset G).symm
    _ ≤ {C : Set M |
        ∃ x ∈ U, C = connectedComponentIn U x ∧ p ∈ closure C}.ncard :=
      Set.ncard_le_ncard hGsubset hbound.1
    _ ≤ 2 := hbound.2


theorem Finset.card_product_filter_closure_le_four
    {p q : M} (A D : Finset (Set M))
    (hA : (A.filter (fun C ↦ p ∈ closure C)).card ≤ 2)
    (hD : (D.filter (fun C ↦ q ∈ closure C)).card ≤ 2) :
    ((A.product D).filter
      (fun z : Set M × Set M ↦ p ∈ closure z.1 ∧ q ∈ closure z.2)).card ≤ 4 := by
  have hsub :
      (A.product D).filter
          (fun z : Set M × Set M ↦ p ∈ closure z.1 ∧ q ∈ closure z.2) ⊆
        (A.filter (fun C ↦ p ∈ closure C)).product
          (D.filter (fun C ↦ q ∈ closure C)) := by
    intro z hz
    have hzprod := Finset.mem_filter.mp hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hzprod.1).1, hzprod.2.1⟩,
        Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hzprod.1).2, hzprod.2.2⟩⟩
  calc
    _ ≤ ((A.filter (fun C ↦ p ∈ closure C)).product
        (D.filter (fun C ↦ q ∈ closure C))).card := Finset.card_le_card hsub
    _ = (A.filter (fun C ↦ p ∈ closure C)).card *
        (D.filter (fun C ↦ q ∈ closure C)).card := Finset.card_product _ _
    _ ≤ 2 * 2 := Nat.mul_le_mul hA hD
    _ = 4 := by norm_num

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[simp]
theorem eval_planeAffinePolynomialEquiv
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (p : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ z i) (planeAffinePolynomialEquiv g p) =
      MvPolynomial.eval (fun i ↦ g z i) p := by
  exact eval_planeAffinePolynomialHom g p z

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic (PlanePoly)


private theorem inline_Esgk_PlanePolynomialRationalPullback__plane_support_sum_le
    {p : PlanePoly} {m : Fin 2 →₀ ℕ} (hm : m ∈ p.support) :
    m 0 + m 1 ≤ p.totalDegree := by
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using
    MvPolynomial.le_totalDegree hm

theorem planePolynomialRationalPullback_totalDegree_le
    (d k : ℕ) (p A B D : PlanePoly) (hp : p.totalDegree ≤ d)
    (hA : A.totalDegree ≤ k) (hB : B.totalDegree ≤ k)
    (hD : D.totalDegree ≤ k) :
    (planePolynomialRationalPullback d p A B D).totalDegree ≤ k * d := by
  classical
  unfold planePolynomialRationalPullback
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  have hsum : m 0 + m 1 ≤ d := (inline_Esgk_PlanePolynomialRationalPullback__plane_support_sum_le hm).trans hp
  have hApow : (A ^ m 0).totalDegree ≤ m 0 * k :=
    (MvPolynomial.totalDegree_pow A _).trans (Nat.mul_le_mul_left _ hA)
  have hBpow : (B ^ m 1).totalDegree ≤ m 1 * k :=
    (MvPolynomial.totalDegree_pow B _).trans (Nat.mul_le_mul_left _ hB)
  have hDpow : (D ^ (d - (m 0 + m 1))).totalDegree ≤
      (d - (m 0 + m 1)) * k :=
    (MvPolynomial.totalDegree_pow D _).trans (Nat.mul_le_mul_left _ hD)
  have hCA : (MvPolynomial.C (p.coeff m) * A ^ m 0).totalDegree ≤ m 0 * k := by
    calc
      _ ≤ (MvPolynomial.C (p.coeff m) : PlanePoly).totalDegree +
          (A ^ m 0).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ m 0 * k := by simpa using hApow
  calc
    _ ≤ (MvPolynomial.C (p.coeff m) * A ^ m 0 * B ^ m 1).totalDegree +
        (D ^ (d - (m 0 + m 1))).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ (m 0 * k + m 1 * k) + (d - (m 0 + m 1)) * k := by
      apply Nat.add_le_add
      · exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hCA hBpow)
      · exact hDpow
    _ = k * d := by
      rw [← Nat.add_mul, ← Nat.add_mul, Nat.add_sub_of_le hsum, Nat.mul_comm]

private theorem inline_Esgk_PlanePolynomialRationalPullback__clear_common_denominator_monomial
    (c x y t : ℝ) (i j d : ℕ) (ht : t ≠ 0) (hij : i + j ≤ d) :
    c * x ^ i * y ^ j * t ^ (d - (i + j)) =
      t ^ d * (c * ((x / t) ^ i * (y / t) ^ j)) := by
  have hpower : t ^ d = t ^ (i + j) * t ^ (d - (i + j)) := by
    rw [← pow_add, Nat.add_sub_of_le hij]
  rw [hpower, pow_add, div_pow, div_pow]
  field_simp

theorem eval_planePolynomialRationalPullback
    (d : ℕ) (p A B D : PlanePoly) (hp : p.totalDegree ≤ d)
    (z : Fin 2 → ℝ) (hD : MvPolynomial.eval z D ≠ 0) :
    MvPolynomial.eval z (planePolynomialRationalPullback d p A B D) =
      (MvPolynomial.eval z D) ^ d *
        MvPolynomial.eval
          ![MvPolynomial.eval z A / MvPolynomial.eval z D,
            MvPolynomial.eval z B / MvPolynomial.eval z D] p := by
  classical
  rw [MvPolynomial.eval_eq' _ p]
  simp only [planePolynomialRationalPullback, map_sum, map_mul, map_pow,
    MvPolynomial.eval_C, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact inline_Esgk_PlanePolynomialRationalPullback__clear_common_denominator_monomial _ _ _ _ _ _ _ hD
    ((inline_Esgk_PlanePolynomialRationalPullback__plane_support_sum_le hm).trans hp)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk

 
theorem continuousOn_of_real_chart
    {X : Type*} [TopologicalSpace X] {C : Set X} {J : Set ℝ}
    (e : C ≃ₜ J) (f : X → ℝ) (he : ∀ p : C, (e p : ℝ) = f p) :
    ContinuousOn f C := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : C ↦ f p)
  have hcont : Continuous (fun p : C ↦ (e p : ℝ)) :=
    continuous_subtype_val.comp e.continuous
  simpa only [he] using hcont


theorem exists_finset_lift_real_chart
    {X : Type*} [TopologicalSpace X] {C : Set X} {J : Set ℝ}
    (e : C ≃ₜ J) (f : X → ℝ) (he : ∀ p : C, (e p : ℝ) = f p)
    (T : Finset ℝ) (hTJ : (T : Set ℝ) ⊆ J) :
    ∃ K : Finset X, (K : Set X) ⊆ C ∧ K.image f = T ∧ K.card = T.card := by
  let g : {t // t ∈ T} → X := fun t ↦ (e.symm ⟨t, hTJ t.property⟩ : X)
  have hfg (t : {t // t ∈ T}) : f (g t) = (t : ℝ) := by
    dsimp [g]
    rw [← he]
    simp
  let K := T.attach.image g
  have hKC : (K : Set X) ⊆ C := by
    intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact (e.symm ⟨t, hTJ t.property⟩).property
  have himage : K.image f = T := by
    ext t
    constructor
    · intro ht
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
      rw [hfg]
      exact q.property
    · intro ht
      let q : {t // t ∈ T} := ⟨t, ht⟩
      refine Finset.mem_image.mpr ⟨g q, ?_, hfg q⟩
      exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ _, rfl⟩
  refine ⟨K, hKC, himage, ?_⟩
  have hcard : (K.image f).card = K.card :=
    Finset.card_image_of_injOn ((injOn_of_real_chart e f he).mono hKC)
  rw [himage] at hcard
  exact hcard.symm


theorem exists_real_chart_sample_cuts
    {X : Type*} [TopologicalSpace X] {C : Set X} {J : Set ℝ}
    (e : C ≃ₜ J) (f : X → ℝ) (he : ∀ p : C, (e p : ℝ) = f p)
    (hJ : J.OrdConnected) (S : Finset X) (hSC : (S : Set X) ⊆ C)
    (k : ℕ) (hk : 0 < k) :
    ∃ K : Finset X,
      (K : Set X) ⊆ C ∧ Disjoint S K ∧ K.card ≤ S.card / k ∧
      (∀ A : Set X, IsPreconnected A → A ⊆ C → Disjoint A (K : Set X) →
        (S.filter (fun x ↦ x ∈ A)).card ≤ k) := by
  have hinj := injOn_of_real_chart e f he
  have hcont := continuousOn_of_real_chart e f he
  have hScard : (S.image f).card = S.card :=
    Finset.card_image_of_injOn (hinj.mono hSC)
  obtain ⟨T, hTcard, hST, hbetween, hload⟩ :=
    exists_finite_real_sample_cuts (S.image f) k hk
  have hSJ : (S.image f : Set ℝ) ⊆ J := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    rw [← he ⟨p, hSC hp⟩]
    exact (e ⟨p, hSC hp⟩).property
  have hTJ : (T : Set ℝ) ⊆ J := by
    intro t ht
    obtain ⟨a, ha, b, hb, hat, htb⟩ := hbetween t ht
    exact hJ.out (hSJ ha) (hSJ hb) ⟨hat.le, htb.le⟩
  obtain ⟨K, hKC, himage, hKcard⟩ := exists_finset_lift_real_chart e f he T hTJ
  refine ⟨K, hKC, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hpS hpK
    apply Finset.disjoint_left.mp hST (Finset.mem_image_of_mem f hpS)
    rw [← himage]
    exact Finset.mem_image_of_mem f hpK
  · simpa only [hKcard, hScard] using hTcard
  · intro A hA hAC hAK
    have hord : (f '' A).OrdConnected := (hA.image f (hcont.mono hAC)).ordConnected
    have hdisj : Disjoint (f '' A) (T : Set ℝ) := by
      apply Set.disjoint_left.mpr
      rintro t ⟨p, hpA, rfl⟩ ht
      have htK : f p ∈ K.image f := by rwa [himage]
      obtain ⟨q, hqK, hqp⟩ := Finset.mem_image.mp htK
      have hqp' : q = p := hinj (hKC hqK) (hAC hpA) hqp
      subst q
      exact Set.disjoint_left.mp hAK hpA hqK
    have hsub : (S.filter (fun x ↦ x ∈ A)).image f ⊆
        (S.image f).filter (fun t ↦ t ∈ f '' A) := by
      intro t ht
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hpS, hpA⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image_of_mem f hpS, ⟨p, hpA, rfl⟩⟩
    have hfilterCard : ((S.filter (fun x ↦ x ∈ A)).image f).card =
        (S.filter (fun x ↦ x ∈ A)).card := by
      apply Finset.card_image_of_injOn
      exact hinj.mono (fun p hp ↦ hSC (Finset.mem_filter.mp hp).1)
    calc
      (S.filter (fun x ↦ x ∈ A)).card =
          ((S.filter (fun x ↦ x ∈ A)).image f).card := hfilterCard.symm
      _ ≤ ((S.image f).filter (fun t ↦ t ∈ f '' A)).card := Finset.card_le_card hsub
      _ ≤ k := hload (f '' A) hord hdisj

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical

namespace Esgk

theorem exists_finite_chart_sample_partition
    {X : Type*} [TopologicalSpace X] {C : Set X} {J : Set ℝ}
    (hCopen : IsOpen C) (hJopen : IsOpen J) (hJord : J.OrdConnected)
    (e : C ≃ₜ J) (f : X → ℝ) (hf : Continuous f)
    (he : ∀ p : C, (e p : ℝ) = f p)
    (S : Finset X) (hSC : (S : Set X) ⊆ C) (k : ℕ) (hk : 0 < k) :
    ∃ K : Finset X, ∃ A : Finset (Set X),
      (K : Set X) ⊆ C ∧
      Disjoint S K ∧
      K.card ≤ S.card / k ∧
      A.card ≤ K.card + 1 ∧
      (∀ V ∈ A, V.Nonempty ∧ IsOpen V ∧ IsConnected V ∧ V ⊆ C ∧
        Disjoint V (K : Set X) ∧
        (S.filter (fun x ↦ x ∈ V)).card ≤ k) ∧
      (A : Set (Set X)).Pairwise Disjoint ∧
      (⋃ V ∈ A, V) = C \ (K : Set X) := by
  obtain ⟨K, hKC, hSK, hKbudget, hload⟩ :=
    exists_real_chart_sample_cuts e f he hJord S hSC k hk
  let T : Finset ℝ := K.image f
  have hinj : Set.InjOn f C := injOn_of_real_chart e f he
  have hTcard : T.card = K.card := by
    dsimp [T]
    exact Finset.card_image_of_injOn (hinj.mono hKC)
  obtain ⟨I, hIcard, hIprops, hIpair, hIunion⟩ :=
    exists_finite_real_cut_intervals J T hJopen hJord
  let lift : Set ℝ → Set X := fun V ↦ C ∩ f ⁻¹' V
  let A : Finset (Set X) := I.image lift
  have hAmem : ∀ V ∈ A, ∃ I₀, I₀ ∈ I ∧ V = lift I₀ := by
    intro V hV
    obtain ⟨I₀, hI₀, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨I₀, hI₀, rfl⟩
  refine ⟨K, A, hKC, hSK, hKbudget, ?_, ?_, ?_, ?_⟩
  · calc
      A.card ≤ I.card := Finset.card_image_le
      _ ≤ T.card + 1 := hIcard
      _ = K.card + 1 := by rw [hTcard]
  · intro V hV
    obtain ⟨I₀, hI₀, rfl⟩ := hAmem V hV
    obtain ⟨hInonempty, hIopen, hIconnected, _hIord, hIsub, hIcut, _⟩ :=
      hIprops I₀ hI₀
    have hVconnected : IsConnected (lift I₀) := by
      exact isConnected_real_chart_slice e f he hIsub hIconnected
    have hVopen : IsOpen (lift I₀) := by
      exact isOpen_real_chart_slice hCopen hf hIopen
    have hVsubset : lift I₀ ⊆ C := inter_subset_left
    have hVdisjoint : Disjoint (lift I₀) (K : Set X) := by
      apply Set.disjoint_left.mpr
      intro p hpV hpK
      exact Set.disjoint_left.mp hIcut hpV.2 (Finset.mem_image_of_mem f hpK)
    have hVload : (S.filter (fun x ↦ x ∈ lift I₀)).card ≤ k := by
      simpa only [lift] using
        hload (lift I₀) hVconnected.isPreconnected hVsubset hVdisjoint
    have hVnonempty : (lift I₀).Nonempty := hVconnected.nonempty
    refine ⟨hVnonempty, hVopen, hVconnected, hVsubset, hVdisjoint, ?_⟩
    simpa only [lift] using hVload
  · intro V hV W hW hVW
    obtain ⟨I₀, hI₀, rfl⟩ := hAmem V hV
    obtain ⟨I₁, hI₁, rfl⟩ := hAmem W hW
    have hIne : I₀ ≠ I₁ := by
      intro hEq
      exact hVW (congrArg lift hEq)
    apply Set.disjoint_left.mpr
    intro p hp₀ hp₁
    exact Set.disjoint_left.mp (hIpair hI₀ hI₁ hIne) hp₀.2 hp₁.2
  · ext p
    constructor
    · intro hp
      obtain ⟨V, hpV⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hVA, hpV⟩ := Set.mem_iUnion.mp hpV
      obtain ⟨I₀, hI₀, rfl⟩ := hAmem V hVA
      have hIcut := (hIprops I₀ hI₀).2.2.2.2.2.1
      refine ⟨hpV.1, ?_⟩
      intro hpK
      exact Set.disjoint_left.mp hIcut hpV.2
        (Finset.mem_image_of_mem f hpK)
    · intro hp
      have hpC : p ∈ C := hp.1
      have hpK : p ∉ (K : Set X) := hp.2
      have hpcoord : f p ∈ J \ (T : Set ℝ) := by
        refine ⟨?_, ?_⟩
        · rw [← he ⟨p, hpC⟩]
          exact (e ⟨p, hpC⟩).property
        · intro hpT
          obtain ⟨q, hqK, hqeq⟩ := Finset.mem_image.mp hpT
          have hqp : q = p := hinj (hKC hqK) hpC hqeq
          exact hpK (hqp ▸ hqK)
      rw [← hIunion] at hpcoord
      obtain ⟨I₀, hpI⟩ := Set.mem_iUnion.mp hpcoord
      obtain ⟨hI₀, hpI⟩ := Set.mem_iUnion.mp hpI
      refine Set.mem_iUnion.mpr ⟨lift I₀, ?_⟩
      refine Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨I₀, hI₀, rfl⟩, ?_⟩
      exact ⟨hpC, hpI⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem affineIsometryTransport_polynomial
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    (C.affineIsometryTransport g).polynomial =
      planeAffinePolynomialEquiv g.symm C.polynomial :=
  rfl


@[simp]
theorem eval_affineIsometryTransport_polynomial
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ z i)
        (C.affineIsometryTransport g).polynomial =
      MvPolynomial.eval (fun i ↦ g.symm z i) C.polynomial := by
  exact eval_planeAffinePolynomialEquiv g.symm C.polynomial z


theorem mem_zeroSet_affineIsometryTransport_iff
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (z : PachDeZeeuw.Algebraic.Point2) :
    z ∈ PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ↔
      g.symm z ∈ PlaneCurveZeroSet C.polynomial := by
  change
    MvPolynomial.eval (fun i ↦ z i)
          (C.affineIsometryTransport g).polynomial = 0 ↔
      MvPolynomial.eval (fun i ↦ g.symm z i) C.polynomial = 0
  rw [C.eval_affineIsometryTransport_polynomial]


theorem affineIsometry_image_zeroSet_eq
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    g '' PlaneCurveZeroSet C.polynomial =
      PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [C.mem_zeroSet_affineIsometryTransport_iff]
    simpa using hx
  · intro hz
    refine ⟨g.symm z, ?_, by simp⟩
    exact (C.mem_zeroSet_affineIsometryTransport_iff g z).mp hz


end IrreduciblePlanePolynomial

end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk


@[simp]
theorem planeIsotropicCoordinateEquiv_symm_apply (p : ComplexPlanePoly) :
    planeIsotropicCoordinateEquiv.symm p = isotropicToPlaneCoordinates p :=
  rfl


@[simp]
theorem isotropicTranslationEquiv_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    isotropicTranslationEquiv ξ p = isotropicTranslation ξ p :=
  rfl

@[simp]
theorem isotropicTranslationEquiv_symm_apply (ξ : ℂ) (p : ComplexPlanePoly) :
    (isotropicTranslationEquiv ξ).symm p = inverseIsotropicTranslation ξ p :=
  rfl

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open scoped EuclideanGeometry


theorem exists_normalizing_isometry_twoAnchor_fiber_dichotomy
    {a c x y : _root_.Point2} (hac : a ≠ c)
    (ha : dist x a ^ 2 = dist y a ^ 2)
    (hc : dist x c ^ 2 = dist y c ^ 2) :
    ∃ (g : _root_.Point2 ≃ᵃⁱ[ℝ] _root_.Point2) (r : ℝ),
      0 < r ∧ g a = xAxisPoint (-r) ∧ g c = xAxisPoint r ∧
        (x = y ∨ ((g x) 0 = (g y) 0 ∧ (g x) 1 = -(g y) 1)) := by
  let r : ℝ := dist a c / 2
  have hr : 0 < r := by
    dsimp [r]
    have hdist : 0 < dist a c := dist_pos.mpr hac
    positivity
  have htarget : dist a c = dist (xAxisPoint (-r)) (xAxisPoint r) := by
    rw [dist_xAxisPoint_neg_eq r hr.le]
    dsimp [r]
    ring
  let g : _root_.Point2 ≃ᵃⁱ[ℝ] _root_.Point2 :=
    directAffineIsometryEquivOfSendPair a c (xAxisPoint (-r)) (xAxisPoint r) hac htarget
  have hga : g a = xAxisPoint (-r) := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_a _ _ _ _ _ _
  have hgc : g c = xAxisPoint r := by
    dsimp [g]
    exact directAffineIsometryEquivOfSendPair_apply_b _ _ _ _ _ _
  have hleft :
      ((g x) 0 + r) ^ 2 + ((g x) 1) ^ 2 =
        ((g y) 0 + r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g x) (xAxisPoint (-r)) ^ 2 =
        dist (g y) (xAxisPoint (-r)) ^ 2 := by
      calc
        dist (g x) (xAxisPoint (-r)) ^ 2 = dist (g x) (g a) ^ 2 := by rw [hga]
        _ = dist x a ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map x a)
        _ = dist y a ^ 2 := ha
        _ = dist (g y) (g a) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map y a)).symm
        _ = dist (g y) (xAxisPoint (-r)) ^ 2 := by rw [hga]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hright :
      ((g x) 0 - r) ^ 2 + ((g x) 1) ^ 2 =
        ((g y) 0 - r) ^ 2 + ((g y) 1) ^ 2 := by
    have hsq : dist (g x) (xAxisPoint r) ^ 2 = dist (g y) (xAxisPoint r) ^ 2 := by
      calc
        dist (g x) (xAxisPoint r) ^ 2 = dist (g x) (g c) ^ 2 := by rw [hgc]
        _ = dist x c ^ 2 := congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map x c)
        _ = dist y c ^ 2 := hc
        _ = dist (g y) (g c) ^ 2 :=
          (congrArg (fun z : ℝ ↦ z ^ 2) (g.dist_map y c)).symm
        _ = dist (g y) (xAxisPoint r) ^ 2 := by rw [hgc]
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] at hsq
    simpa [xAxisPoint, Fin.sum_univ_two, Real.dist_eq] using hsq
  have hfiber := twoAnchor_sqDistance_eq_same_or_reflection hr hleft hright
  refine ⟨g, r, hr, hga, hgc, ?_⟩
  rcases hfiber with hsame | hreflect
  · left
    apply g.injective
    ext i
    fin_cases i
    · exact hsame.1
    · exact hsame.2
  · exact Or.inr hreflect

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open scoped BigOperators

namespace Esgk


private lemma inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective :
    Function.Injective (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) := by
  rw [← MvPolynomial.aeval_eq_eval]
  exact (MvPolynomial.aeval_injective_iff_of_isEmpty.mpr (RingHom.injective _))

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero
    (r : MvPolynomial (Fin 1) ℝ) (hr : r ≠ 0) :
    Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r) ≠ 0 := by
  apply (Polynomial.map_ne_zero_iff inline_Esgk_SharpResultantFiniteSetCount__remainingEval_injective).mpr
  intro h
  apply hr
  exact (MvPolynomial.finSuccEquiv ℝ 0).injective h

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le
    (r : MvPolynomial (Fin 1) ℝ) :
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
      r.totalDegree := by
  calc
    (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)).natDegree ≤
        (headCurry r).natDegree := Polynomial.natDegree_map_le
    _ = MvPolynomial.degreeOf 0 r := by
      simpa [headCurry] using (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 0) r)
    _ ≤ r.totalDegree := MvPolynomial.degreeOf_le_totalDegree r 0

private lemma inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero
    (r : MvPolynomial (Fin 1) ℝ) (z : Fin 2 → ℝ)
    (hz : MvPolynomial.eval (fun i : Fin 1 ↦ z i.succ) r = 0) :
    Polynomial.eval (z 1)
      (Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)) = 0 := by
  have hcoords :
      (fun i : Fin 1 ↦ z i.succ) = Fin.cons (z 1) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval := by
    funext i
    fin_cases i
    rfl
  rw [hcoords] at hz
  simpa using
    (MvPolynomial.eval_eq_eval_mv_eval' (R := ℝ) bundle_Esgk_SharpResultantFiniteSetCount_remainingEval (z 1) r).symm ▸ hz


theorem common_zero_finset_card_le_totalDegree_mul
    (p q : MvPolynomial (Fin 2) ℝ) (S : Finset (Fin 2 → ℝ))
    (hpDegree : 0 < (headCurry p).natDegree)
    (hresultant : headResultant p q ≠ 0)
    (hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (S : Set (Fin 2 → ℝ)))
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let r := headResultant p q
  let u : Polynomial ℝ := Polynomial.map (MvPolynomial.eval bundle_Esgk_SharpResultantFiniteSetCount_remainingEval) (headCurry r)
  let T : Finset ℝ := S.image (fun z : Fin 2 → ℝ ↦ z 1)
  have hcard : S.card = T.card := by
    exact (Finset.card_image_iff.mpr hprojection).symm
  have hr : r ≠ 0 := by
    simpa [r] using hresultant
  have hu : u ≠ 0 := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_ne_zero r hr
  have hTsubset : (T : Set ℝ) ⊆ u.rootSet ℝ := by
    intro y hy
    change y ∈ T at hy
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hy
    rw [Polynomial.mem_rootSet_of_ne hu]
    exact inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_eval_eq_zero r z
      (eval_headResultant_eq_zero_of_common_zero p q z hpDegree
        (hzero z hzS).1 (hzero z hzS).2)
  have hTcard : T.card ≤ u.natDegree := by
    rw [← Set.ncard_coe_finset T]
    exact (Set.ncard_le_ncard hTsubset).trans (Polynomial.ncard_rootSet_le u ℝ)
  have huDegree : u.natDegree ≤ r.totalDegree := by
    simpa [u] using inline_Esgk_SharpResultantFiniteSetCount__headResultant_univariate_natDegree_le r
  rw [hcard]
  exact hTcard.trans huDegree |>.trans
    (headResultant_totalDegree_le_totalDegree_mul p q)

end Esgk
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology


lemma evalPlane_rename_swap (h : PlanePoly) (x y : ℝ) :
    evalPlane (MvPolynomial.rename (Equiv.swap 0 1) h) (x, y) = evalPlane h (y, x) := by
  unfold evalPlane
  rw [MvPolynomial.eval_rename]
  have hcoords :
      ((fun i : Fin 2 => if i = 0 then (x, y).1 else (x, y).2) ∘ (Equiv.swap 0 1)) =
        (fun i : Fin 2 => if i = 0 then (y, x).1 else (y, x).2) := by
    funext i
    fin_cases i <;> simp [Function.comp]
  rw [hcoords]


end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearPoint_apply (s : ℝ) (p : ℝ × ℝ) :
    shearPoint s p = (p.1 - s * p.2, p.2) := rfl


theorem evalPlane_shearPoly_shearPoint (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p := by
   
  set pt : Fin 2 → ℝ :=
    (fun i => if i = 0 then (shearPoint s p).1 else (shearPoint s p).2) with hpt
   
  have h1 : evalPlane (shearPoly s h) (shearPoint s p)
      = (MvPolynomial.aeval pt) (MvPolynomial.aeval (shearVars s) h) := by
    rw [shearPoly, evalPlane, MvPolynomial.aeval_eq_eval]
  rw [h1]
   
   
  rw [MvPolynomial.comp_aeval_apply]
   
  have hpt0 : pt 0 = p.1 - s * p.2 := rfl
  have hpt1 : pt 1 = p.2 := rfl
   
  have hvars : (fun i => (MvPolynomial.aeval pt) (shearVars s i))
      = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
    funext i
    fin_cases i
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
          = p.1
      rw [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self_apply, hpt0, hpt1]
      ring
    ·  
      show (MvPolynomial.aeval pt) (MvPolynomial.X 1) = p.2
      rw [MvPolynomial.aeval_X, hpt1]
  rw [hvars, evalPlane, MvPolynomial.aeval_eq_eval]


theorem totalDegree_aeval_le {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  have hsum : MvPolynomial.aeval f p
      = ∑ v ∈ p.support, MvPolynomial.aeval f (MvPolynomial.monomial v (MvPolynomial.coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro v hv
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ v.support, (f i ^ v i).totalDegree
      ≤ ∑ i ∈ v.support, v i * (f i).totalDegree :=
        Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ i ∈ v.support, v i * 1 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (le_refl (v i)) (hf i))
    _ = v.sum (fun _ e => e) := by simp only [mul_one]; rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv


lemma shearVars_totalDegree_le (s : ℝ) (i : Fin 2) : (shearVars s i).totalDegree ≤ 1 := by
  unfold shearVars
  split
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact le_of_eq (totalDegree_X 0)
    · exact (totalDegree_mul _ _).trans (le_of_eq (by rw [totalDegree_C, totalDegree_X]))
  · exact le_of_eq (totalDegree_X 1)


theorem shearPoly_totalDegree_le (s : ℝ) (h : PlanePoly) :
    (shearPoly s h).totalDegree ≤ h.totalDegree := by
  unfold shearPoly
  exact totalDegree_aeval_le (shearVars s) (shearVars_totalDegree_le s) h

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set
open scoped Classical BigOperators

namespace Esgk


theorem exists_finite_chart_partition_aggregation
    {X : Type*} [TopologicalSpace X]
    (U : Set X) (F : Finset (Set X))
    (hFopen : ∀ C ∈ F, IsOpen C)
    (hFdisj : (F : Set (Set X)).Pairwise Disjoint)
    (hFcover : (⋃ C ∈ F, C) = U)
    (f : X → ℝ) (hf : Continuous f)
    (hcharts : ∀ C ∈ F, ∃ J : Set ℝ, IsOpen J ∧ J.OrdConnected ∧
      ∃ e : C ≃ₜ J, ∀ p : C, (e p : ℝ) = f p)
    (P : Finset X) (hPU : (P : Set X) ⊆ U) (k : ℕ) (hk : 0 < k) :
    ∃ K : Finset X, ∃ A : Finset (Set X),
      (K : Set X) ⊆ U ∧ Disjoint P K ∧ K.card ≤ P.card / k ∧
      A.card ≤ K.card + F.card ∧
      (∀ V ∈ A, V.Nonempty ∧ IsOpen V ∧ IsConnected V ∧ V ⊆ U ∧
        Disjoint V (K : Set X) ∧ (P.filter (fun x ↦ x ∈ V)).card ≤ k) ∧
      (A : Set (Set X)).Pairwise Disjoint ∧
      (⋃ V ∈ A, V) = U \ (K : Set X) := by
  let I := {C // C ∈ F}
  let Pc : I → Finset X := fun c ↦ P.filter (fun x ↦ x ∈ (c : Set X))
  have hdomains : Pairwise (fun c d : I ↦ Disjoint (c : Set X) (d : Set X)) := by
    intro c d hcd
    apply hFdisj c.property d.property
    intro heq
    exact hcd (Subtype.ext heq)
  have hcoverPoint (p : X) : p ∈ U ↔ ∃ c : I, p ∈ (c : Set X) := by
    constructor
    · intro hp
      rw [← hFcover] at hp
      obtain ⟨C, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hCF, hp⟩ := Set.mem_iUnion.mp hp
      exact ⟨⟨C, hCF⟩, hp⟩
    · rintro ⟨c, hp⟩
      rw [← hFcover]
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨c.property, hp⟩⟩
  have hCU (c : I) : (c : Set X) ⊆ U := fun p hp ↦ (hcoverPoint p).mpr ⟨c, hp⟩
  have hdata : ∀ c : I, ∃ K : Finset X, ∃ A : Finset (Set X),
      (K : Set X) ⊆ (c : Set X) ∧ Disjoint (Pc c) K ∧
      K.card ≤ (Pc c).card / k ∧ A.card ≤ K.card + 1 ∧
      (∀ V ∈ A, V.Nonempty ∧ IsOpen V ∧ IsConnected V ∧ V ⊆ (c : Set X) ∧
        Disjoint V (K : Set X) ∧ ((Pc c).filter (fun x ↦ x ∈ V)).card ≤ k) ∧
      (A : Set (Set X)).Pairwise Disjoint ∧
      (⋃ V ∈ A, V) = (c : Set X) \ (K : Set X) := by
    intro c
    obtain ⟨J, hJopen, hJord, e, he⟩ := hcharts c c.property
    exact exists_finite_chart_sample_partition (hFopen c c.property) hJopen hJord
      e f hf he (Pc c) (fun _ hp ↦ (Finset.mem_filter.mp hp).2) k hk
  choose Kc Ac hKC hPcK hKbudget hAcard hAprops hApair hAunion using hdata
  let K := Finset.univ.biUnion Kc
  let A := Finset.univ.biUnion Ac
  have hKmem (p : X) : p ∈ K ↔ ∃ c : I, p ∈ Kc c := by
    simp only [K, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hAmem (V : Set X) : V ∈ A ↔ ∃ c : I, V ∈ Ac c := by
    simp only [A, Finset.mem_biUnion, Finset.mem_univ, true_and]
  have hKdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint Kc := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro p hpc hpd
    exact Set.disjoint_left.mp (hdomains hcd) (hKC c hpc) (hKC d hpd)
  have hKcard : K.card = ∑ c : I, (Kc c).card := Finset.card_biUnion hKdisj
  have hPcdisj : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint Pc := by
    intro c _ d _ hcd
    apply Finset.disjoint_left.mpr
    intro p hpc hpd
    exact Set.disjoint_left.mp (hdomains hcd)
      (Finset.mem_filter.mp hpc).2 (Finset.mem_filter.mp hpd).2
  have hPunion : Finset.univ.biUnion Pc = P := by
    ext p
    constructor
    · intro hp
      obtain ⟨c, _, hpc⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_filter.mp hpc).1
    · intro hp
      obtain ⟨c, hpc⟩ := (hcoverPoint p).mp (hPU hp)
      exact Finset.mem_biUnion.mpr
        ⟨c, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hp, hpc⟩⟩
  have hPcard : (∑ c : I, (Pc c).card) = P.card := by
    rw [← Finset.card_biUnion hPcdisj, hPunion]
  have hKU : (K : Set X) ⊆ U := by
    intro p hp
    obtain ⟨c, hpc⟩ := (hKmem p).mp hp
    exact hCU c (hKC c hpc)
  have hPK : Disjoint P K := by
    apply Finset.disjoint_left.mpr
    intro p hpP hpK
    obtain ⟨c, hpc⟩ := (hKmem p).mp hpK
    exact Finset.disjoint_left.mp (hPcK c)
      (Finset.mem_filter.mpr ⟨hpP, hKC c hpc⟩) hpc
  have hbudget : K.card ≤ P.card / k := by
    apply (Nat.le_div_iff_mul_le hk).mpr
    rw [hKcard, Finset.sum_mul]
    calc
      (∑ c : I, (Kc c).card * k) ≤ ∑ c : I, (Pc c).card :=
        Finset.sum_le_sum (fun c _ ↦ (Nat.le_div_iff_mul_le hk).mp (hKbudget c))
      _ = P.card := hPcard
  have hcount : A.card ≤ K.card + F.card := by
    calc
      A.card ≤ ∑ c : I, (Ac c).card := Finset.card_biUnion_le
      _ ≤ ∑ c : I, ((Kc c).card + 1) := Finset.sum_le_sum (fun c _ ↦ hAcard c)
      _ = (∑ c : I, (Kc c).card) + F.card := by
        simp [Finset.sum_add_distrib, I]
      _ = K.card + F.card := by rw [hKcard]
  have hprops : ∀ V ∈ A,
      V.Nonempty ∧ IsOpen V ∧ IsConnected V ∧ V ⊆ U ∧
        Disjoint V (K : Set X) ∧ (P.filter (fun x ↦ x ∈ V)).card ≤ k := by
    intro V hVA
    obtain ⟨c, hVc⟩ := (hAmem V).mp hVA
    obtain ⟨hVne, hVo, hVconn, hVC, hVKc, hVload⟩ := hAprops c V hVc
    refine ⟨hVne, hVo, hVconn, hVC.trans (hCU c), ?_, ?_⟩
    · apply Set.disjoint_left.mpr
      intro p hpV hpK
      obtain ⟨d, hpd⟩ := (hKmem p).mp hpK
      by_cases hcd : c = d
      · subst d
        exact Set.disjoint_left.mp hVKc hpV hpd
      · exact Set.disjoint_left.mp (hdomains hcd) (hVC hpV) (hKC d hpd)
    · have hfilter : (Pc c).filter (fun x ↦ x ∈ V) = P.filter (fun x ↦ x ∈ V) := by
        ext p
        simp only [Pc, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hpP, _⟩, hpV⟩
          exact ⟨hpP, hpV⟩
        · rintro ⟨hpP, hpV⟩
          exact ⟨⟨hpP, hVC hpV⟩, hpV⟩
      rwa [hfilter] at hVload
  refine ⟨K, A, hKU, hPK, hbudget, hcount, hprops, ?_, ?_⟩
  · intro V hVA W hWA hVW
    obtain ⟨c, hVc⟩ := (hAmem V).mp hVA
    obtain ⟨d, hWd⟩ := (hAmem W).mp hWA
    by_cases hcd : c = d
    · subst d
      exact hApair c hVc hWd hVW
    · apply Set.disjoint_left.mpr
      intro p hpV hpW
      exact Set.disjoint_left.mp (hdomains hcd)
        ((hAprops c V hVc).2.2.2.1 hpV) ((hAprops d W hWd).2.2.2.1 hpW)
  · ext p
    constructor
    · intro hp
      obtain ⟨V, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hVA, hpV⟩ := Set.mem_iUnion.mp hp
      have hV := hprops V hVA
      exact ⟨hV.2.2.2.1 hpV, fun hpK ↦ Set.disjoint_left.mp hV.2.2.2.2.1 hpV hpK⟩
    · rintro ⟨hpU, hpK⟩
      obtain ⟨c, hpc⟩ := (hcoverPoint p).mp hpU
      have hpnot : p ∉ Kc c := fun h ↦ hpK ((hKmem p).mpr ⟨c, h⟩)
      have hplocal : p ∈ (⋃ V ∈ Ac c, V) := by
        rw [hAunion c]
        exact ⟨hpc, hpnot⟩
      obtain ⟨V, hp⟩ := Set.mem_iUnion.mp hplocal
      obtain ⟨hVc, hpV⟩ := Set.mem_iUnion.mp hp
      exact Set.mem_iUnion.mpr ⟨V, Set.mem_iUnion.mpr ⟨(hAmem V).mpr ⟨c, hVc⟩, hpV⟩⟩

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial

 
theorem bidegreeBound_iff_degreeOf_le {R : Type*} [CommSemiring R] (m : ℕ)
    (Q : BidegreePolynomial R) :
    BidegreeBound m Q ↔ degreeOf 0 Q ≤ m ∧ degreeOf 1 Q ≤ m := by
  constructor
  · intro hQ
    constructor <;> rw [degreeOf_le_iff] <;> intro e he
    · exact (hQ e he).1
    · exact (hQ e he).2
  · rintro ⟨hzero, hone⟩ e he
    exact ⟨degreeOf_le_iff.mp hzero e he, degreeOf_le_iff.mp hone e he⟩

 
theorem isotropicTranslation_monomial (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    isotropicTranslation ξ (monomial e c) =
      C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1 := by
  rw [isotropicTranslation, eval₂Hom_monomial, Finsupp.prod_fintype]
  · simp [Fin.prod_univ_two, mul_assoc]
  · intro i
    simp

 
theorem degreeOf_isotropicTranslation_monomial_le (ξ : ℂ) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (i : Fin 2) : degreeOf i (isotropicTranslation ξ (monomial e c)) ≤ e i := by
  rw [isotropicTranslation_monomial]
  fin_cases i
  · have hzero : degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using degreeOf_sub_le 0 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (0 : Fin 2) ≠ 1 by decide] using
        degreeOf_sub_le 0 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 0 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 0 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 0
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 0 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ e 0 * degreeOf 0 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 1 := Nat.mul_le_mul_left _ hzero
        _ = e 0 := Nat.mul_one _
    have hpowOne' :
        degreeOf 0 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ 0 := by
      calc
        _ ≤ e 1 * degreeOf 0 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 0 := Nat.mul_le_mul_left _ hone
        _ = 0 := Nat.mul_zero _
    have hmulLeft' :
        degreeOf 0 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ e 0 := by
      calc
        _ ≤ degreeOf 0 (C c : BidegreePolynomial ℂ) +
            degreeOf 0 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + e 0 := Nat.add_le_add (by simp) hpowZero'
        _ = e 0 := Nat.zero_add _
    calc
      degreeOf 0 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 0 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 0 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ e 0 + 0 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 0 := Nat.add_zero _
  · have hzero : degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) ≤ 0 := by
      simpa [degreeOf_X, show (1 : Fin 2) ≠ 0 by decide] using
        degreeOf_sub_le 1 (X 0 : BidegreePolynomial ℂ) (C ξ)
    have hone : degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) ≤ 1 := by
      simpa using
        degreeOf_sub_le 1 (X 1 : BidegreePolynomial ℂ) (C (star ξ))
    have hpowZero := degreeOf_pow_le 1 (X 0 - C ξ : BidegreePolynomial ℂ) (e 0)
    have hpowOne := degreeOf_pow_le 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) (e 1)
    have hmulLeft :=
      degreeOf_mul_le 1 (C c : BidegreePolynomial ℂ) ((X 0 - C ξ) ^ e 0)
    have hmul := degreeOf_mul_le 1
      ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0)
      ((X 1 - C (star ξ)) ^ e 1)
    have hpowZero' : degreeOf 1 ((X 0 - C ξ : BidegreePolynomial ℂ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ e 0 * degreeOf 1 (X 0 - C ξ : BidegreePolynomial ℂ) := hpowZero
        _ ≤ e 0 * 0 := Nat.mul_le_mul_left _ hzero
        _ = 0 := Nat.mul_zero _
    have hpowOne' :
        degreeOf 1 ((X 1 - C (star ξ) : BidegreePolynomial ℂ) ^ e 1) ≤ e 1 := by
      calc
        _ ≤ e 1 * degreeOf 1 (X 1 - C (star ξ) : BidegreePolynomial ℂ) := hpowOne
        _ ≤ e 1 * 1 := Nat.mul_le_mul_left _ hone
        _ = e 1 := Nat.mul_one _
    have hmulLeft' :
        degreeOf 1 ((C c : BidegreePolynomial ℂ) * (X 0 - C ξ) ^ e 0) ≤ 0 := by
      calc
        _ ≤ degreeOf 1 (C c : BidegreePolynomial ℂ) +
            degreeOf 1 ((X 0 - C ξ) ^ e 0) := hmulLeft
        _ ≤ 0 + 0 := Nat.add_le_add (by simp) hpowZero'
        _ = 0 := Nat.zero_add _
    calc
      degreeOf 1 (C c * (X 0 - C ξ) ^ e 0 * (X 1 - C (star ξ)) ^ e 1)
          ≤ degreeOf 1 (C c * (X 0 - C ξ) ^ e 0) +
              degreeOf 1 ((X 1 - C (star ξ)) ^ e 1) := hmul
      _ ≤ 0 + e 1 := Nat.add_le_add hmulLeft' hpowOne'
      _ = e 1 := Nat.zero_add _

 
theorem degreeOf_isotropicTranslation_le (ξ : ℂ) (Q : BidegreePolynomial ℂ) (i : Fin 2) :
    degreeOf i (isotropicTranslation ξ Q) ≤ degreeOf i Q := by
  conv_lhs => rw [Q.as_sum]
  rw [map_sum]
  refine (degreeOf_sum_le i Q.support fun e ↦
    isotropicTranslation ξ (monomial e (coeff e Q))).trans ?_
  rw [degreeOf_eq_sup]
  exact Finset.sup_le fun e he ↦
    (degreeOf_isotropicTranslation_monomial_le ξ e (coeff e Q) i).trans
      (Finset.le_sup (f := fun d : Fin 2 →₀ ℕ ↦ d i) he)


theorem bidegreeBound_isotropicTranslation (ξ : ℂ) (m : ℕ) {Q : BidegreePolynomial ℂ}
    (hQ : BidegreeBound m Q) : BidegreeBound m (isotropicTranslation ξ Q) := by
  rw [bidegreeBound_iff_degreeOf_le] at hQ ⊢
  exact ⟨(degreeOf_isotropicTranslation_le ξ Q 0).trans hQ.1,
    (degreeOf_isotropicTranslation_le ξ Q 1).trans hQ.2⟩

 
theorem totalDegree_le_two_mul_of_bidegreeBound {R : Type*} [CommSemiring R] (m : ℕ)
    {Q : BidegreePolynomial R} (hQ : BidegreeBound m Q) : totalDegree Q ≤ 2 * m := by
  rw [totalDegree]
  refine Finset.sup_le fun e he ↦ ?_
  have hzero := (hQ e he).1
  have hone := (hQ e he).2
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)]
  simp only [Fin.sum_univ_two]
  omega


end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem planeAffinePolynomialEquiv_symm_apply_squaredDistance
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    planeAffinePolynomialEquiv g.symm (planeSquaredDistancePolynomial a) =
      planeSquaredDistancePolynomial (g a) := by
  apply MvPolynomial.funext
  intro z
  let x : PachDeZeeuw.Algebraic.Point2 := WithLp.toLp 2 z
  calc
    MvPolynomial.eval z
        (planeAffinePolynomialEquiv g.symm
          (planeSquaredDistancePolynomial a)) =
        dist (g.symm x) a ^ 2 := by
      rw [eval_planeAffinePolynomialEquiv]
      simp [x]
    _ = dist x (g a) ^ 2 := by
      have hdist := g.dist_map (g.symm x) a
      apply congrArg (fun t : ℝ ↦ t ^ 2)
      simpa using hdist.symm
    _ = MvPolynomial.eval z
        (planeSquaredDistancePolynomial (g a)) := by
      simpa [x] using (eval_planeSquaredDistancePolynomial (g a) x).symm


@[simp]
theorem planeSquaredDistancePolynomial_xAxisPoint (r : ℝ) :
    planeSquaredDistancePolynomial (xAxisPoint r) =
      (MvPolynomial.X 0 - MvPolynomial.C r) ^ 2 +
        MvPolynomial.X 1 ^ 2 := by
  simp [planeSquaredDistancePolynomial, xAxisPoint]

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial


theorem totalDegree_eval₂Hom_le_of_isHomogeneous_one
    {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ r, (f r).IsHomogeneous 0)
    (hg : ∀ i, (g i).IsHomogeneous 1)
    (P : MvPolynomial σ R) :
    ((MvPolynomial.eval₂Hom f g) P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [← P.sum_homogeneousComponent]
  rw [map_sum (MvPolynomial.eval₂Hom f g)]
  refine MvPolynomial.totalDegree_finsetSum_le (d := P.totalDegree) ?_
  intro d hd
  have hhom :=
    (MvPolynomial.homogeneousComponent_isHomogeneous d P).eval₂ f g hf hg
  have hterm :
      ((MvPolynomial.eval₂Hom f g)
        (MvPolynomial.homogeneousComponent d P)).totalDegree ≤ d := by
    simpa only [MvPolynomial.coe_eval₂Hom, Nat.one_mul] using hhom.totalDegree_le
  have hle : d ≤ P.totalDegree := by
    simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
  exact hterm.trans hle

private theorem inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] i : ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
  · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
      (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _

private theorem inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous
    (i : Fin 2) :
    (![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
        MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1] i :
      ComplexPlanePoly).IsHomogeneous 1 := by
  fin_cases i
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).add
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)
  · exact (MvPolynomial.isHomogeneous_X ℂ 0).sub
      ((MvPolynomial.isHomogeneous_X ℂ 1).C_mul _)

 
theorem planeToIsotropicCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__planeToIsotropicCoordinates_image_isHomogeneous P

 
theorem isotropicToPlaneCoordinates_totalDegree_le (P : ComplexPlanePoly) :
    (isotropicToPlaneCoordinates P).totalDegree ≤ P.totalDegree := by
  exact totalDegree_eval₂Hom_le_of_isHomogeneous_one
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.X 0 + MvPolynomial.C Complex.I * MvPolynomial.X 1,
      MvPolynomial.X 0 - MvPolynomial.C Complex.I * MvPolynomial.X 1]
    (fun c ↦ MvPolynomial.isHomogeneous_C (σ := Fin 2) c)
    inline_Esgk_PlaneIsotropicDegree__isotropicToPlaneCoordinates_image_isHomogeneous P

 
theorem planeToIsotropicCoordinates_totalDegree (P : ComplexPlanePoly) :
    (planeToIsotropicCoordinates P).totalDegree = P.totalDegree := by
  apply Nat.le_antisymm (planeToIsotropicCoordinates_totalDegree_le P)
  have hcomp :
      isotropicToPlaneCoordinates (planeToIsotropicCoordinates P) = P :=
    RingHom.congr_fun
      isotropicToPlaneCoordinates_comp_planeToIsotropicCoordinates P
  calc
    P.totalDegree =
        (isotropicToPlaneCoordinates (planeToIsotropicCoordinates P)).totalDegree := by
      rw [hcomp]
    _ ≤ (planeToIsotropicCoordinates P).totalDegree :=
      isotropicToPlaneCoordinates_totalDegree_le _


end Esgk
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology


scoped notation "E" => chartEquiv

 
@[simp] theorem chartEquiv_apply (x : PachDeZeeuw.Algebraic.Point2) : chartEquiv x = (x 0, x 1) := rfl

 
@[simp] theorem chartEquiv_fst (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).1 = x 0 := rfl

 
@[simp] theorem chartEquiv_snd (x : PachDeZeeuw.Algebraic.Point2) : (chartEquiv x).2 = x 1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_zero (z : ℝ × ℝ) :
    (chartEquiv.symm z) 0 = z.1 := rfl

 
@[simp] theorem chartEquiv_symm_apply_one (z : ℝ × ℝ) :
    (chartEquiv.symm z) 1 = z.2 := rfl


theorem eval_eq_evalPlane_chart (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i => x i) p = evalPlane p (chartEquiv x) := by
  unfold evalPlane
  refine congrArg (fun f => MvPolynomial.eval f p) ?_
  funext i
  fin_cases i <;> simp


end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


@[simp] lemma shearAlgEquiv_apply (s : ℝ) (h : PlanePoly) :
    shearAlgEquiv s h = shearPoly s h := by
  rw [shearAlgEquiv, AlgEquiv.ofAlgHom_apply]
  rfl


theorem irreducible_shearPoly_iff (s : ℝ) (h : PlanePoly) :
    Irreducible (shearPoly s h) ↔ Irreducible h := by
  rw [← shearAlgEquiv_apply s h]
  exact MulEquiv.irreducible_iff (shearAlgEquiv s)

end PachDeZeeuw.Algebraic

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq (m : Fin 2 →₀ ℕ) : (m.sum fun _ e => e) = m 0 + m 1 := by
  rw [Finsupp.sum, ← Finsupp.degree_apply, Finsupp.degree_eq_sum, Fin.sum_univ_two]

 
private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single (D : ℕ) :
    ∑ i ∈ (Finsupp.single (1 : Fin 2) D).support, (Finsupp.single (1 : Fin 2) D) i = D := by
  rw [← Finsupp.degree_apply, Finsupp.degree_single]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow (s : ℝ) (a : ℕ) :
    coeff (Finsupp.single (1 : Fin 2) a) ((X 0 + C s * X 1) ^ a) = s ^ a := by
  classical
  induction a with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, coeff_add]
    have hX0 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * X 0) = 0 := by
      rw [coeff_mul_X', if_neg]; simp [Finsupp.mem_support_iff]
    have hX1 : coeff (Finsupp.single (1 : Fin 2) (n + 1)) ((X 0 + C s * X 1) ^ n * (C s * X 1))
        = s ^ (n + 1) := by
      rw [show (X 0 + C s * X 1 : PlanePoly) ^ n * (C s * X 1)
            = C s * ((X 0 + C s * X 1) ^ n * X 1) by ring, coeff_C_mul,
          show (Finsupp.single (1 : Fin 2) (n + 1))
            = (Finsupp.single (1 : Fin 2) n) + (Finsupp.single (1 : Fin 2) 1) by
              rw [← Finsupp.single_add], coeff_mul_X, ih]
      ring
    rw [hX0, hX1, zero_add]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    shearPoly s (monomial m c) = C c * (X 0 + C s * X 1) ^ (m 0) * (X 1) ^ (m 1) := by
  unfold shearPoly shearVars
  rw [aeval_monomial, MvPolynomial.algebraMap_eq,
    Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp only [Fin.prod_univ_two, Fin.isValue, if_true, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  ring


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial (s : ℝ) (m : Fin 2 →₀ ℕ) (c : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) (m 0 + m 1)) (shearPoly s (monomial m c))
      = c * s ^ (m 0) := by
  classical
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__shear_monomial, X_pow_eq_monomial, mul_assoc, coeff_C_mul,
    show (Finsupp.single (1 : Fin 2) (m 0 + m 1))
        = (Finsupp.single (1 : Fin 2) (m 0)) + (Finsupp.single (1 : Fin 2) (m 1)) by
        rw [← Finsupp.single_add],
    coeff_mul_monomial, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_single_one_pow, mul_one]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt (s : ℝ) (D : ℕ) (m : Fin 2 →₀ ℕ) (c : ℝ)
    (hlt : m 0 + m 1 < D) :
    coeff (Finsupp.single (1 : Fin 2) D) (shearPoly s (monomial m c)) = 0 := by
  apply coeff_eq_zero_of_totalDegree_lt
  rw [inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__sum_support_single]
  refine lt_of_le_of_lt (shearPoly_totalDegree_le s (monomial m c)) ?_
  refine lt_of_le_of_lt (totalDegree_monomial_le m c) ?_
  rw [Function.id_def, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq]
  exact hlt


theorem coeff_yD_shear_eq_eval (h : PlanePoly) (s : ℝ) :
    coeff (Finsupp.single (1 : Fin 2) h.totalDegree) (shearPoly s h)
      = (shearTopPoly h).eval s := by
  classical
  set D := h.totalDegree with hD
  have hexp : shearPoly s h
      = ∑ m ∈ h.support, shearPoly s (monomial m (coeff m h)) := by
    conv_lhs => rw [h.as_sum]
    rw [shearPoly, map_sum]
    rfl
  rw [hexp, coeff_sum, shearTopPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  have hle : m 0 + m 1 ≤ D := by
    rw [hD, ← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m]; exact le_totalDegree hm
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [if_pos (heq.trans hD)]
    have hidx : (Finsupp.single (1 : Fin 2) D) = Finsupp.single (1 : Fin 2) (m 0 + m 1) := by
      rw [heq]
    rw [hidx, inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  · rw [if_neg (by omega), inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_shear_monomial_lt s D m (coeff m h) hlt]
    simp


theorem shearTopPoly_ne_zero (h : PlanePoly) (hh : h ≠ 0) : shearTopPoly h ≠ 0 := by
  classical
  set D := h.totalDegree with hD
  have hne : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m0, hm0, hsup⟩ :=
    Finset.exists_mem_eq_sup h.support hne (fun s => s.sum fun _ e => e)
  have hm0deg : m0 0 + m0 1 = D := by rw [← inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__msum_eq m0, ← hsup]; rfl
  have hcoeff0 : coeff m0 h ≠ 0 := MvPolynomial.mem_support_iff.mp hm0
  intro hzero
  apply hcoeff0
  have hkey : (shearTopPoly h).coeff (m0 0) = coeff m0 h := by
    rw [shearTopPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single m0]
    · rw [if_pos hm0deg, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro m _ hmm0
      by_cases hmd : m 0 + m 1 = D
      · rw [if_pos hmd, Polynomial.coeff_C_mul_X_pow, if_neg]
        intro hm00
        apply hmm0
        have hm00' : m 0 = m0 0 := hm00.symm
        have hm1 : m 1 = m0 1 := by omega
        apply Finsupp.ext
        intro i
        match i with
        | 0 => exact hm00'
        | 1 => exact hm1
      · rw [if_neg hmd, Polynomial.coeff_zero]
    · intro hm
      exact absurd hm0 (by rw [MvPolynomial.notMem_support_iff] at hm ⊢; exact hm)
  rw [hzero, Polynomial.coeff_zero] at hkey
  exact hkey.symm


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (i : Fin 2) (g : PlanePoly) (m : Fin 2 →₀ ℕ) :
    coeff m (X i * pderiv i g) = (m i) • coeff m g := by
  classical
  have hexp : X i * pderiv i g
      = ∑ v ∈ g.support, (v i) • monomial v (coeff v g) := by
    conv_lhs => rw [g.as_sum]
    rw [map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [X_mul_pderiv_monomial]
  rw [hexp, coeff_sum]
  simp only [coeff_smul, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · rw [if_pos rfl]
  · intro v _ hvm
    rw [if_neg (fun h => hvm h), smul_zero]
  · intro hm
    rw [notMem_support_iff] at hm
    rw [if_pos rfl, hm, smul_zero]


private theorem inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (g : PlanePoly) (D : ℕ) (hD : 1 ≤ D)
    (h0 : pderiv (1 : Fin 2) g = 0) :
    coeff (Finsupp.single (1 : Fin 2) D) g = 0 := by
  have hco := inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_X_mul_pderiv (1 : Fin 2) g (Finsupp.single (1 : Fin 2) D)
  rw [h0, mul_zero, coeff_zero] at hco
  rw [Finsupp.single_eq_same, nsmul_eq_mul] at hco
  have hDpos : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact (mul_eq_zero.mp hco.symm).resolve_left hDpos


theorem partialY_shearPoly_finite_bad (h : PlanePoly) (hpos : 1 ≤ h.totalDegree) :
    {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}.Finite := by
  have hh : h ≠ 0 := by
    intro h0
    rw [h0, totalDegree_zero] at hpos
    exact absurd hpos (by norm_num)
  have hPne : shearTopPoly h ≠ 0 := shearTopPoly_ne_zero h hh
  apply Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hPne)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
   
  rw [Polynomial.IsRoot.def, ← coeff_yD_shear_eq_eval]
  exact inline_LeanFormalizations_PachDeZeeuw_CrossingLemma_ShearPartialY__coeff_yD_eq_zero_of_pderiv_eq_zero (shearPoly s h) h.totalDegree hpos hs

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial


@[simp]
theorem squaredDistanceClassAt_xAxisPoint_neg
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceClassAt (xAxisPoint (-r)) =
      C.leftSquaredDistanceClass r := by
  simp [squaredDistanceClassAt, leftSquaredDistanceClass, coordinateClass]
  rw [← MvPolynomial.algebraMap_eq]
  rw [Ideal.Quotient.mk_algebraMap]

@[simp]
theorem squaredDistanceClassAt_xAxisPoint
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceClassAt (xAxisPoint r) =
      C.rightSquaredDistanceClass r := by
  simp [squaredDistanceClassAt, rightSquaredDistanceClass, coordinateClass]
  rw [← MvPolynomial.algebraMap_eq]
  rw [Ideal.Quotient.mk_algebraMap]

@[simp]
theorem squaredDistanceFunctionAt_xAxisPoint_neg
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceFunctionAt (xAxisPoint (-r)) =
      algebraMap C.CoordinateRing C.FunctionField
        (C.leftSquaredDistanceClass r) := by
  rw [squaredDistanceFunctionAt, C.squaredDistanceClassAt_xAxisPoint_neg]

@[simp]
theorem squaredDistanceFunctionAt_xAxisPoint
    (C : IrreduciblePlanePolynomial ℝ) (r : ℝ) :
    C.squaredDistanceFunctionAt (xAxisPoint r) =
      algebraMap C.CoordinateRing C.FunctionField
        (C.rightSquaredDistanceClass r) := by
  rw [squaredDistanceFunctionAt, C.squaredDistanceClassAt_xAxisPoint]


@[simp]
theorem affineIsometryCoordinateRingAlgEquiv_apply_squaredDistanceClassAt
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    C.affineIsometryCoordinateRingAlgEquiv g
        (C.squaredDistanceClassAt a) =
      (C.affineIsometryTransport g).squaredDistanceClassAt (g a) := by
  change
    C.coordinateRingAlgEquivTransport (planeAffinePolynomialEquiv g.symm)
        (Ideal.Quotient.mk _ (planeSquaredDistancePolynomial a)) =
      Ideal.Quotient.mk _ (planeSquaredDistancePolynomial (g a))
  rw [C.coordinateRingAlgEquivTransport_apply_mk]
  rw [planeAffinePolynomialEquiv_symm_apply_squaredDistance]


@[simp]
theorem affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a : PachDeZeeuw.Algebraic.Point2) :
    C.affineIsometryFunctionFieldAlgEquiv g
        (C.squaredDistanceFunctionAt a) =
      (C.affineIsometryTransport g).squaredDistanceFunctionAt (g a) := by
  change
    C.functionFieldAlgEquivTransport (planeAffinePolynomialEquiv g.symm)
        (algebraMap C.CoordinateRing C.FunctionField
          (C.squaredDistanceClassAt a)) =
      algebraMap (C.affineIsometryTransport g).CoordinateRing
        (C.affineIsometryTransport g).FunctionField
        ((C.affineIsometryTransport g).squaredDistanceClassAt (g a))
  rw [C.functionFieldAlgEquivTransport_apply_algebraMap]
  congr 1
  exact C.affineIsometryCoordinateRingAlgEquiv_apply_squaredDistanceClassAt g a


theorem affineIsometryFunctionFieldAlgEquiv_apply_squaredDistance_pair
    (C : IrreduciblePlanePolynomial ℝ)
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (a c : PachDeZeeuw.Algebraic.Point2) (r : ℝ)
    (hga : g a = xAxisPoint (-r))
    (hgc : g c = xAxisPoint r) :
    C.affineIsometryFunctionFieldAlgEquiv g
          (C.squaredDistanceFunctionAt a) =
        algebraMap (C.affineIsometryTransport g).CoordinateRing
          (C.affineIsometryTransport g).FunctionField
          ((C.affineIsometryTransport g).leftSquaredDistanceClass r) ∧
      C.affineIsometryFunctionFieldAlgEquiv g
          (C.squaredDistanceFunctionAt c) =
        algebraMap (C.affineIsometryTransport g).CoordinateRing
          (C.affineIsometryTransport g).FunctionField
          ((C.affineIsometryTransport g).rightSquaredDistanceClass r) := by
  constructor
  · rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt]
    rw [hga]
    exact (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint_neg r
  · rw [C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistanceFunctionAt]
    rw [hgc]
    exact (C.affineIsometryTransport g).squaredDistanceFunctionAt_xAxisPoint r


theorem exists_affineIsometryTransport_normalizedDistancePair
    (C : IrreduciblePlanePolynomial ℝ) {a c : PachDeZeeuw.Algebraic.Point2} (hac : a ≠ c) :
    ∃ (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (r : ℝ),
      0 < r ∧
        g a = xAxisPoint (-r) ∧
        g c = xAxisPoint r ∧
        g '' PlaneCurveZeroSet C.polynomial =
          PlaneCurveZeroSet (C.affineIsometryTransport g).polynomial ∧
        (C.affineIsometryFunctionFieldAlgEquiv g
              (C.squaredDistanceFunctionAt a) =
            algebraMap (C.affineIsometryTransport g).CoordinateRing
              (C.affineIsometryTransport g).FunctionField
              ((C.affineIsometryTransport g).leftSquaredDistanceClass r) ∧
          C.affineIsometryFunctionFieldAlgEquiv g
              (C.squaredDistanceFunctionAt c) =
            algebraMap (C.affineIsometryTransport g).CoordinateRing
              (C.affineIsometryTransport g).FunctionField
              ((C.affineIsometryTransport g).rightSquaredDistanceClass r)) := by
  obtain ⟨g, r, hr, hga, hgc, _⟩ :=
    exists_normalizing_isometry_twoAnchor_fiber_dichotomy
      (a := a) (c := c) (x := a) (y := a) hac rfl rfl
  refine ⟨g, r, hr, hga, hgc, C.affineIsometry_image_zeroSet_eq g, ?_⟩
  exact C.affineIsometryFunctionFieldAlgEquiv_apply_squaredDistance_pair
    g a c r hga hgc

end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial


theorem isCoprime_fraction_map_of_primitive_irreducible_not_dvd
    (P Q : Polynomial XCoeff)
    (hPprim : P.IsPrimitive)
    (hPirr : Irreducible P)
    (hnot : ¬ P ∣ Q) :
    IsCoprime (P.map (algebraMap XCoeff XFrac))
      (Q.map (algebraMap XCoeff XFrac)) := by
  have hPmapIrr : Irreducible (P.map (algebraMap XCoeff XFrac)) :=
    hPprim.irreducible_iff_irreducible_map_fraction_map.mp hPirr
  rw [hPmapIrr.coprime_iff_not_dvd]
  intro hmap
  by_cases hQzero : Q = 0
  · exact hnot (hQzero ▸ dvd_zero P)
  have hcontent : Q.content ≠ 0 := by
    intro hzero
    exact hQzero (Polynomial.content_eq_zero_iff.mp hzero)
  have hcontentMapUnit :
      IsUnit (Polynomial.C (algebraMap XCoeff XFrac Q.content)) := by
    apply Polynomial.isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    apply hcontent
    exact IsFractionRing.injective XCoeff XFrac (by simpa using hzero)
  have hmapPrimPart :
      P.map (algebraMap XCoeff XFrac) ∣ Q.primPart.map (algebraMap XCoeff XFrac) := by
    apply (IsUnit.dvd_mul_left hcontentMapUnit).mp
    rw [← Polynomial.map_C, ← Polynomial.map_mul, ← Q.eq_C_content_mul_primPart]
    exact hmap
  have hprimPart : P ∣ Q.primPart :=
    hPprim.dvd_of_fraction_map_dvd_fraction_map hmapPrimPart
  exact hnot (dvd_trans hprimPart Q.primPart_dvd)

end PachDeZeeuw.Algebraic

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem headResultant_ne_zero_of_irreducible_not_dvd
    (p q : PlanePoly)
    (hpDegree : 0 < (headCurry p).natDegree)
    (hirr : Irreducible p)
    (hnot : ¬ p ∣ q) :
    headResultant p q ≠ 0 := by
  have hprimitive : (Curry0 p).IsPrimitive := by
    apply curry_isPrimitive_of_irreducible_positive_natDegree p hirr
    simpa only [Curry0, headCurry] using hpDegree
  have hcoprime :
      IsCoprime
        ((Curry0 p).map (algebraMap XCoeff XFrac))
        ((Curry0 q).map (algebraMap XCoeff XFrac)) := by
    exact isCoprime_fraction_map_of_primitive_irreducible_not_dvd
      (Curry0 p) (Curry0 q)
      hprimitive
      (by
        simpa [Curry0] using
          (hirr.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv))
      (by
        intro hdiv
        apply hnot
        have hdiv' := map_dvd (MvPolynomial.finSuccEquiv ℝ 1).symm hdiv
        simpa [Curry0] using hdiv')
  simpa [headResultant, headCurry, Curry0] using
    (resultant_ne_zero_of_fraction_coprime (Curry0 p) (Curry0 q) hcoprime)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem planeRadialQuadratic_isHomogeneous :
    MvPolynomial.IsHomogeneous planeRadialQuadratic 2 := by
  exact
    (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (0 : Fin 2) 2).add
      (MvPolynomial.isHomogeneous_X_pow (R := ℝ) (1 : Fin 2) 2)


theorem planeSquaredDistancePolynomial_eq_radial_linear_constant (a : PachDeZeeuw.Algebraic.Point2) :
    planeSquaredDistancePolynomial a =
      planeRadialQuadratic -
        MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 -
        MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 +
        MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) := by
  simp only [planeSquaredDistancePolynomial, planeRadialQuadratic, map_add, map_mul, map_pow,
    map_ofNat]
  ring


theorem homogeneousComponent_two_planeSquaredDistancePolynomial (a : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.homogeneousComponent 2 (planeSquaredDistancePolynomial a) =
      planeRadialQuadratic := by
  have hlinear0 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 0) * MvPolynomial.X 0 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (0 : Fin 2)).C_mul _
  have hlinear1 :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (2 * a 1) * MvPolynomial.X 1 : PlanePoly) 1 :=
    (MvPolynomial.isHomogeneous_X (R := ℝ) (1 : Fin 2)).C_mul _
  have hconstant :
      MvPolynomial.IsHomogeneous
        (MvPolynomial.C (a 0 ^ 2 + a 1 ^ 2) : PlanePoly) 0 :=
    MvPolynomial.isHomogeneous_C _ _
  rw [planeSquaredDistancePolynomial_eq_radial_linear_constant]
  rw [map_add, map_sub, map_sub]
  rw [MvPolynomial.homogeneousComponent_of_mem planeRadialQuadratic_isHomogeneous,
    MvPolynomial.homogeneousComponent_of_mem hlinear0,
    MvPolynomial.homogeneousComponent_of_mem hlinear1,
    MvPolynomial.homogeneousComponent_of_mem hconstant]
  norm_num

private theorem inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a : ℝ) (k : Fin 2) :
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤ 2 := by
  calc
    ((MvPolynomial.X k - MvPolynomial.C a) ^ 2 : PlanePoly).totalDegree ≤
        2 * (MvPolynomial.X k - MvPolynomial.C a : PlanePoly).totalDegree :=
      MvPolynomial.totalDegree_pow _ _
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 (by
      simpa using
        (MvPolynomial.totalDegree_sub
          (MvPolynomial.X k : PlanePoly) (MvPolynomial.C a)))
    _ = 2 := by omega

 
theorem planeSquaredDistancePolynomial_totalDegree_le (a : PachDeZeeuw.Algebraic.Point2) :
    (planeSquaredDistancePolynomial a).totalDegree ≤ 2 := by
  rw [planeSquaredDistancePolynomial]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 0) 0)
      (inline_Esgk_PlaneRadialQuadratic__totalDegree_X_sub_C_sq_le_two (a 1) 1))

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_C (s a : ℝ) :
    shearPoly s (C a) = C a := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_zero (s : ℝ) :
    shearPoly s 0 = 0 := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_add (s : ℝ) (p q : PlanePoly) :
    shearPoly s (p + q) = shearPoly s p + shearPoly s q := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_mul (s : ℝ) (p q : PlanePoly) :
    shearPoly s (p * q) = shearPoly s p * shearPoly s q := by
  simp [shearPoly]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_X_zero (s : ℝ) :
    shearPoly s (X (0 : Fin 2)) = X 0 + C s * X 1 := by
  simp [shearPoly, shearVars]

@[simp] private theorem inline_Esgk_PlaneShearSingularTransport__shearPoly_X_one (s : ℝ) :
    shearPoly s (X (1 : Fin 2)) = X 1 := by
  simp [shearPoly, shearVars]


theorem pderiv_one_shearPoly (s : ℝ) (h : PlanePoly) :
    pderiv (1 : Fin 2) (shearPoly s h) =
      C s * shearPoly s (pderiv (0 : Fin 2) h) +
        shearPoly s (pderiv (1 : Fin 2) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, mul_add]; ring
  | mul_X p i hp =>
      fin_cases i <;> simp [hp] <;> ring


theorem pderiv_zero_shearPoly (s : ℝ) (h : PlanePoly) :
    pderiv (0 : Fin 2) (shearPoly s h) =
      shearPoly s (pderiv (0 : Fin 2) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      fin_cases i <;> simp [hp]


theorem eval_shearPoly_shearPoint_chart (s : ℝ) (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval
        (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
        (shearPoly s h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply,
    evalPlane_shearPoly_shearPoint, ← eval_eq_evalPlane_chart]


theorem singularPoint_shearPoint
    (s : ℝ) (h : PlanePoly) {z : PachDeZeeuw.Algebraic.Point2}
    (hz : z ∈ SingularPointSet h) :
    chartEquiv.symm (shearPoint s (chartEquiv z)) ∈
      SingularPointSet (shearPoly s h) := by
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact eval_shearPoly_shearPoint_chart s h z |>.trans hz.1.1
  · rw [pderiv_zero_shearPoly]
    exact eval_shearPoly_shearPoint_chart s (pderiv (0 : Fin 2) h) z |>.trans hz.1.2
  · have hzero :
        MvPolynomial.eval
            (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
            (shearPoly s (pderiv (0 : Fin 2) h)) = 0 :=
      eval_shearPoly_shearPoint_chart s (pderiv (0 : Fin 2) h) z |>.trans hz.1.2
    have hone :
        MvPolynomial.eval
            (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
            (shearPoly s (pderiv (1 : Fin 2) h)) = 0 :=
      eval_shearPoly_shearPoint_chart s (pderiv (1 : Fin 2) h) z |>.trans hz.2
    change MvPolynomial.eval
        (fun i ↦ (chartEquiv.symm (shearPoint s (chartEquiv z))) i)
        (pderiv (1 : Fin 2) (shearPoly s h)) = 0
    rw [pderiv_one_shearPoly]
    simp only [map_add, map_mul, MvPolynomial.eval_C]
    rw [hzero, hone]
    ring

 
theorem eval_rename_swap_swapPoint (h : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ swapPoint z i)
        (MvPolynomial.rename (Equiv.swap 0 1) h) =
      MvPolynomial.eval (fun i ↦ z i) h := by
  rw [MvPolynomial.eval_rename]
  have hcoords :
      ((fun i ↦ swapPoint z i) ∘ (Equiv.swap 0 1)) = fun i ↦ z i := by
    funext i
    fin_cases i <;> simp [Function.comp, swapPoint, mkPoint2]
  rw [hcoords]


theorem singularPoint_swap
    (h : PlanePoly) {z : PachDeZeeuw.Algebraic.Point2} (hz : z ∈ SingularPointSet h) :
    swapPoint z ∈
      SingularPointSet (MvPolynomial.rename (Equiv.swap 0 1) h) := by
  rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hz ⊢
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact eval_rename_swap_swapPoint h z |>.trans hz.1.1
  · have hrename :
        pderiv (0 : Fin 2) (MvPolynomial.rename (Equiv.swap 0 1) h) =
          MvPolynomial.rename (Equiv.swap 0 1) (pderiv (1 : Fin 2) h) := by
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective
          (x := (1 : Fin 2)) (p := h))
    rw [hrename]
    exact eval_rename_swap_swapPoint (pderiv (1 : Fin 2) h) z |>.trans hz.2
  · have hrename :
        pderiv (1 : Fin 2) (MvPolynomial.rename (Equiv.swap 0 1) h) =
          MvPolynomial.rename (Equiv.swap 0 1) (pderiv (0 : Fin 2) h) := by
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective
          (x := (0 : Fin 2)) (p := h))
    rw [hrename]
    exact eval_rename_swap_swapPoint (pderiv (0 : Fin 2) h) z |>.trans hz.1.2

end PachDeZeeuw.Algebraic
end

end


section
set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace PachDeZeeuw.Algebraic

open MvPolynomial


theorem sepPoly_eval (p q : ℝ × ℝ) (s : ℝ) :
    (sepPoly p q).eval s = (p.1 - q.1) - s * (p.2 - q.2) := by
  simp only [sepPoly, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring


theorem sepPoly_ne_zero {p q : ℝ × ℝ} (hpq : p ≠ q) : sepPoly p q ≠ 0 := by
  intro hzero
  by_cases hy : p.2 = q.2
  ·  
    have hx : p.1 ≠ q.1 := by
      intro hx
      exact hpq (Prod.ext hx hy)
    have hcoeff : (sepPoly p q).coeff 0 = p.1 - q.1 := by
      simp only [sepPoly, hy, sub_self, map_zero, zero_mul, sub_zero]
      rw [Polynomial.coeff_C, if_pos rfl]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact (sub_ne_zero.mpr hx) hcoeff.symm
  ·  
    have hcoeff : (sepPoly p q).coeff 1 = -(p.2 - q.2) := by
      rw [sepPoly, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by norm_num),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_sub]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    have : p.2 - q.2 = 0 := by linarith [neg_eq_zero.mp hcoeff.symm]
    exact (sub_ne_zero.mpr hy) this


theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P := by
  classical
   
  set B₁ : Set ℝ := ⋃ h ∈ Γ, {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}
    with hB₁
  have hB₁_fin : B₁.Finite := by
    rw [hB₁]
    refine Set.Finite.biUnion (Finset.finite_toSet Γ) ?_
    intro h hh
    exact partialY_shearPoly_finite_bad h (hpos h hh)
   
  set B₂ : Set ℝ := ⋃ pq ∈ P.offDiag, {s : ℝ | (sepPoly pq.1 pq.2).IsRoot s} with hB₂
  have hB₂_fin : B₂.Finite := by
    rw [hB₂]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOfPred_isRoot (sepPoly_ne_zero hne)
   
  obtain ⟨s, hs⟩ := (hB₁_fin.union hB₂_fin).exists_notMem
  rw [Set.mem_union, not_or] at hs
  obtain ⟨hs₁, hs₂⟩ := hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  ·  
    intro h hh hpd
    apply hs₁
    rw [hB₁, Set.mem_iUnion₂]
    exact ⟨h, hh, hpd⟩
  ·  
    intro h hh
    exact (shearPoly_totalDegree_le s h).trans (hdeg h hh)
  ·  
    intro h hh
    exact (irreducible_shearPoly_iff s h).mpr (hirr h hh)
  ·  
    intro p hp q hq hpqeq
    by_contra hpq
     
    apply hs₂
    rw [hB₂, Set.mem_iUnion₂]
    refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq, hpq⟩, ?_⟩
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, sepPoly_eval]
     
    simp only [shearPoint_apply] at hpqeq
    linarith [hpqeq]

end PachDeZeeuw.Algebraic

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic _root_.Polynomial


@[simp]
theorem affineLineParam_apply (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) (i : Fin 2) :
    affineLineParam x v t i = x i + t * v i := by
  simp [affineLineParam]


private theorem inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineCoordinatePolynomial
    (x v : PachDeZeeuw.Algebraic.Point2) (i : Fin 2) (t : ℝ) :
    eval t (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v i) = affineLineParam x v t i := by
  rw [affineLineParam_apply]
  simp [bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial]
  ring

private theorem inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le
    (x v : PachDeZeeuw.Algebraic.Point2) (i : Fin 2) :
    (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v i).natDegree ≤ 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  rw [bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial, Polynomial.coeff_add,
    Polynomial.coeff_C_of_ne_zero hn0, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_of_ne_one hn1]
  simp


private theorem inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineRestrictedMonomial_le
    (x v : PachDeZeeuw.Algebraic.Point2) (i j : ℕ) (a : ℝ) :
    (bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial x v i j a).natDegree ≤ i + j := by
  have hcoeff : (C a : Polynomial ℝ).natDegree ≤ 0 := by
    simp
  have hfirst :
      (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 0 ^ i).natDegree ≤ i := by
    simpa using Polynomial.natDegree_pow_le_of_le i
      (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le x v 0)
  have hsecond :
      (bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 1 ^ j).natDegree ≤ j := by
    simpa using Polynomial.natDegree_pow_le_of_le j
      (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineCoordinatePolynomial_le x v 1)
  have hfirstProduct :
      (C a * bundle_Esgk_AffineLinePolynomialRestriction_affineLineCoordinatePolynomial x v 0 ^ i).natDegree ≤ i := by
    simpa using Polynomial.natDegree_mul_le_of_le hcoeff hfirst
  exact Polynomial.natDegree_mul_le_of_le hfirstProduct hsecond

private theorem inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineRestrictedMonomial
    (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) (i j : ℕ) (a : ℝ) :
    eval t (bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial x v i j a) =
      a * (affineLineParam x v t 0) ^ i * (affineLineParam x v t 1) ^ j := by
  simp [bundle_Esgk_AffineLinePolynomialRestriction_affineLineRestrictedMonomial, inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineCoordinatePolynomial]


theorem natDegree_affineLinePolynomialRestriction_le
    (p : PlanePoly) (x v : PachDeZeeuw.Algebraic.Point2) (d : ℕ) (hdegree : p.totalDegree ≤ d) :
    (affineLinePolynomialRestriction p x v).natDegree ≤ d := by
  rw [affineLinePolynomialRestriction, MvPolynomial.sum_def]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro exponent hexponent
  apply (inline_Esgk_AffineLinePolynomialRestriction__natDegree_affineLineRestrictedMonomial_le x v
    (exponent 0) (exponent 1) (p.coeff exponent)).trans
  have htotal := (MvPolynomial.le_totalDegree hexponent).trans hdegree
  simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using htotal


theorem eval_affineLinePolynomialRestriction
    (p : PlanePoly) (x v : PachDeZeeuw.Algebraic.Point2) (t : ℝ) :
    eval t (affineLinePolynomialRestriction p x v) =
      MvPolynomial.eval (fun i ↦ affineLineParam x v t i) p := by
  rw [affineLinePolynomialRestriction, MvPolynomial.sum_def,
    Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [inline_Esgk_AffineLinePolynomialRestriction__eval_affineLineRestrictedMonomial]
  simp [Fin.prod_univ_two, mul_assoc]


theorem exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet
    (x : PachDeZeeuw.Algebraic.Point2) {v z : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0)
    (hz : z ∈ PlaneCurveZeroSet (affineLinePolynomial x v)) :
    ∃ t : ℝ, affineLineParam x v t = z := by
  rw [mem_PlaneCurveZeroSet, affineLinePolynomial_eval] at hz
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i
      · exact hv0
      · exact hv1
    have hxprod : v 1 * (z 0 - x 0) = 0 := by
      simpa [hv0] using hz
    have hx : x 0 = z 0 := by
      have := (mul_eq_zero.mp hxprod).resolve_left hv1
      linarith
    let t := (z 1 - x 1) / v 1
    have ht0 : affineLineParam x v t 0 = z 0 := by
      simp [t, hv0, hx]
    have ht1 : affineLineParam x v t 1 = z 1 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv1]
      ring
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    · exact ht0
    · exact ht1
  · let t := (z 0 - x 0) / v 0
    have ht0 : affineLineParam x v t 0 = z 0 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv0]
      ring
    have ht1 : affineLineParam x v t 1 = z 1 := by
      rw [affineLineParam_apply]
      dsimp [t]
      field_simp [hv0]
      ring_nf at hz ⊢
      linarith
    refine ⟨t, ?_⟩
    ext i
    fin_cases i
    · exact ht0
    · exact ht1


theorem affineLinePolynomialRestriction_ne_zero_of_not_subset
    (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) {v : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0)
    (hnot : ¬ PlaneCurveZeroSet (affineLinePolynomial x v) ⊆ PlaneCurveZeroSet p) :
    affineLinePolynomialRestriction p x v ≠ 0 := by
  intro hrestriction
  apply hnot
  intro z hz
  rw [mem_PlaneCurveZeroSet]
  obtain ⟨t, rfl⟩ :=
    exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet x hv hz
  have heval := eval_affineLinePolynomialRestriction p x v t
  rw [hrestriction] at heval
  simpa using heval.symm


theorem finite_affineLine_zeroSet_card_le_of_not_subset
    (p : PlanePoly) (x : PachDeZeeuw.Algebraic.Point2) {v : PachDeZeeuw.Algebraic.Point2} (d : ℕ) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hv : v ≠ 0) (hdegree : p.totalDegree ≤ d)
    (hzero : ∀ z ∈ S, MvPolynomial.eval (fun i ↦ z i) p = 0)
    (hline : ∀ z ∈ S, z ∈ PlaneCurveZeroSet (affineLinePolynomial x v))
    (hnot : ¬ PlaneCurveZeroSet (affineLinePolynomial x v) ⊆ PlaneCurveZeroSet p) :
    S.card ≤ d := by
  let H := affineLinePolynomialRestriction p x v
  have hrestriction : H ≠ 0 := by
    exact affineLinePolynomialRestriction_ne_zero_of_not_subset p x hv hnot
  have hdegreeH : H.natDegree ≤ d := by
    exact natDegree_affineLinePolynomialRestriction_le p x v d hdegree
  apply le_trans
    (card_le_natDegree_of_parametrized_roots S H (affineLineParam x v) ?_)
    hdegreeH
  intro z hz
  obtain ⟨t, ht⟩ :=
    exists_affineLineParam_eq_of_mem_affineLinePolynomial_zeroSet x hv (hline z hz)
  refine ⟨t, ?_, ht⟩
  rw [Multiset.mem_toFinset]
  apply (Polynomial.mem_roots hrestriction).2
  rw [Polynomial.IsRoot.def]
  rw [show H = affineLinePolynomialRestriction p x v by rfl]
  rw [eval_affineLinePolynomialRestriction]
  simpa [ht] using hzero z hz

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem planeRadialQuadratic_ne_zero : planeRadialQuadratic ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ if i = 0 then (1 : ℝ) else 0)) hzero
  simp [planeRadialQuadratic] at heval


end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


@[simp]
theorem affineCircularChart_X_zero (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [affineCircularChart]

@[simp]
theorem affineCircularChart_X_one (c : ℂ) :
    affineCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [affineCircularChart]

@[simp]
theorem projectiveCircularChart_X_zero (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 0) = 1 := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_one (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 1) = MvPolynomial.C c + circularChartU := by
  simp [projectiveCircularChart]

@[simp]
theorem projectiveCircularChart_X_two (c : ℂ) :
    projectiveCircularChart c (MvPolynomial.X 2) = circularChartZ := by
  simp [projectiveCircularChart]


theorem projectiveCircularChart_realPlanePolynomialProjectiveEmbedding
    (c : ℂ) (p : PlanePoly) :
    projectiveCircularChart c (realPlanePolynomialProjectiveEmbedding p) =
      affineCircularChart c p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
      realToComplexPlanePolynomial, affineCircularChart, projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [realPlanePolynomialProjectiveEmbedding, complexPlanePolynomialEmbedding,
          realToComplexPlanePolynomial]


theorem projectiveCircularChart_planeHomogenizedLayer
    (c : ℂ) (D d : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenizedLayer D d p) =
      circularChartZ ^ (D - d) *
        affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  rw [planeHomogenizedLayer, map_mul, map_pow,
    projectiveCircularChart_realPlanePolynomialProjectiveEmbedding]
  simp [projectivePlaneZ, mul_comm]


theorem projectiveCircularChart_planeHomogenization
    (c : ℂ) (D : ℕ) (p : PlanePoly) :
    projectiveCircularChart c (planeHomogenization D p) =
      ∑ d ∈ Finset.range (D + 1),
        circularChartZ ^ (D - d) *
          affineCircularChart c (MvPolynomial.homogeneousComponent d p) := by
  simp only [planeHomogenization, map_sum, projectiveCircularChart_planeHomogenizedLayer]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial _root_.Polynomial


theorem resultant_vanishes_at_common_zero_of_first_positive
    (p q : PlanePoly) {z : PachDeZeeuw.Algebraic.Point2}
    (hp0deg : 0 < (Curry0 p).natDegree)
    (hz : z ∈ PlaneCurveZeroSet p ∩ PlaneCurveZeroSet q) :
    coeffCoord z ∈ CoeffRootSet (ResultantCoeff p q) := by
  rw [CoeffRootSet]
  have hp : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) p) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.1
  have hq : Polynomial.eval (elimCoord z) (Specialized0 (coeffCoord z) q) = 0 := by
    rw [← eval_eq_specialized_eval]
    exact hz.2
  have hm :
      (Specialized0 (coeffCoord z) p).natDegree ≤ (Curry0 p).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le
        (f := coeffEval (coeffCoord z)) (p := Curry0 p))
  have hn :
      (Specialized0 (coeffCoord z) q).natDegree ≤ (Curry0 q).natDegree := by
    simpa [Specialized0] using
      (Polynomial.natDegree_map_le
        (f := coeffEval (coeffCoord z)) (p := Curry0 q))
  obtain ⟨u, v, hu, hv, hbez⟩ :=
    Polynomial.exists_mul_add_mul_eq_C_resultant
      (f := Specialized0 (coeffCoord z) p)
      (g := Specialized0 (coeffCoord z) q) hm hn
      (Or.inl (Nat.ne_of_gt hp0deg))
  have hzero :
      Polynomial.eval (elimCoord z)
        (Polynomial.C
          (Polynomial.resultant (Specialized0 (coeffCoord z) p)
            (Specialized0 (coeffCoord z) q)
            (Curry0 p).natDegree (Curry0 q).natDegree)) = 0 := by
    rw [← hbez]
    simp [hp, hq]
  simpa [ResultantCoeff, Specialized0, coeffEval] using hzero


theorem curry0_natDegree_pos_of_pderiv_zero_ne
    (p : PlanePoly) (hpartial : pderiv (0 : Fin 2) p ≠ 0) :
    0 < (Curry0 p).natDegree := by
  have hdegree_ne : MvPolynomial.degreeOf (0 : Fin 2) p ≠ 0 := by
    intro hzero
    apply hpartial
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact not_not_intro hzero
  have hcurry_degree :
      (Curry0 p).natDegree = MvPolynomial.degreeOf (0 : Fin 2) p := by
    simpa [Curry0] using
      (MvPolynomial.natDegree_finSuccEquiv (R := ℝ) (n := 1) (f := p))
  rw [hcurry_degree]
  exact Nat.pos_of_ne_zero hdegree_ne


theorem resultantCoeff_pderiv_zero_ne
    (p : PlanePoly) (hirr : Irreducible p)
    (hpartial : pderiv (0 : Fin 2) p ≠ 0) :
    ResultantCoeff p (pderiv (0 : Fin 2) p) ≠ 0 := by
  have hpositive := curry0_natDegree_pos_of_pderiv_zero_ne p hpartial
  have hprimitive : (Curry0 p).IsPrimitive :=
    curry_isPrimitive_of_irreducible_positive_natDegree p hirr hpositive
  have hcurry_irreducible : Irreducible (Curry0 p) := by
    simpa [Curry0] using
      hirr.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv
  have hfraction_irreducible :
      Irreducible ((Curry0 p).map (algebraMap XCoeff XFrac)) :=
    hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hcurry_irreducible
  have hcoprime :
      IsCoprime
        ((Curry0 p).map (algebraMap XCoeff XFrac))
        ((Curry0 (pderiv (0 : Fin 2) p)).map (algebraMap XCoeff XFrac)) := by
    have hseparable :
        ((Curry0 p).map (algebraMap XCoeff XFrac)).Separable :=
      hfraction_irreducible.separable
    change IsCoprime
      ((Curry0 p).map (algebraMap XCoeff XFrac))
      (Polynomial.derivative
        ((Curry0 p).map (algebraMap XCoeff XFrac))) at hseparable
    simpa [curry0_pderiv0, Polynomial.derivative_map] using hseparable
  exact resultant_ne_zero_of_fraction_coprime
    (Curry0 p) (Curry0 (pderiv (0 : Fin 2) p)) hcoprime


end PachDeZeeuw.Algebraic
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw


theorem preparedSecondCurvePolynomial_ne_zero {d : ℕ}
    (X : PreparedBipartiteInput d) :
    preparedSecondCurvePolynomial X ≠ 0 :=
  (Classical.choose_spec X.hC₂).1

theorem preparedSecondCurvePolynomial_totalDegree_le {d : ℕ}
    (X : PreparedBipartiteInput d) :
    (preparedSecondCurvePolynomial X).totalDegree ≤ d :=
  (Classical.choose_spec X.hC₂).2.1


theorem preparedSecondCurvePolynomial_zeroSet {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.C₂ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet
      (preparedSecondCurvePolynomial X) := by
  simpa [preparedSecondCurvePolynomial,
    PachDeZeeuw.Algebraic.PlaneCurveZeroSet] using
    (Classical.choose_spec X.hC₂).2.2.2


theorem encodedAuxPoint_injective : Function.Injective encodedAuxPoint := by
  intro p q hpq
  have hfirst : decodedAuxFirst (encodedAuxPoint p) =
      decodedAuxFirst (encodedAuxPoint q) := congrArg decodedAuxFirst hpq
  have hsecond : decodedAuxSecond (encodedAuxPoint p) =
      decodedAuxSecond (encodedAuxPoint q) := congrArg decodedAuxSecond hpq
  exact Prod.ext (by simpa using hfirst) (by simpa using hsecond)


theorem prepared_first_second_dist_pos {d : ℕ}
    (X : PreparedBipartiteInput d) (i : X.P₁) {p : PachDeZeeuw.Algebraic.Point2}
    (hp : p ∈ X.P₂) :
    0 < dist (i : PachDeZeeuw.Algebraic.Point2) p := by
  apply dist_pos.mpr
  intro hip
  have hi : (i : PachDeZeeuw.Algebraic.Point2) ∈ (X.P₁ : Set PachDeZeeuw.Algebraic.Point2) := by simp
  have hpSet : p ∈ (X.P₂ : Set PachDeZeeuw.Algebraic.Point2) := by simpa using hp
  have hpFirst : p ∈ (X.P₁ : Set PachDeZeeuw.Algebraic.Point2) := by simpa [hip] using hi
  exact Set.disjoint_left.mp X.assumption31.pointSetsDisjoint hpFirst hpSet


theorem sharpAuxiliaryCircleFiberBound_of_noncontainment
    (hnoncontainment : AuxiliaryDistanceCircleNoncontainmentStatement) :
    SharpAuxiliaryCircleFiberBoundStatement := by
  intro d X ij p hp
  apply finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    (preparedSecondCurvePolynomial X) (ij.2 : PachDeZeeuw.Algebraic.Point2)
      (dist (ij.1 : PachDeZeeuw.Algebraic.Point2) p) d (auxDistancePartners X ij p)
  · exact prepared_first_second_dist_pos X ij.1 hp
  · exact preparedSecondCurvePolynomial_totalDegree_le X
  · intro q hq
    have hfilter := Finset.mem_filter.mp hq
    have hqCurve : q ∈ X.C₂ := X.hP₂ (by simpa using hfilter.1)
    rw [preparedSecondCurvePolynomial_zeroSet X] at hqCurve
    exact hqCurve
  · intro q hq
    have hrelation := (Finset.mem_filter.mp hq).2
    change dist q (ij.2 : PachDeZeeuw.Algebraic.Point2) = dist (ij.1 : PachDeZeeuw.Algebraic.Point2) p
    simpa [dist_comm] using hrelation.symm
  · exact hnoncontainment d X ij p hp


theorem auxDistancePairsWithCurveLabel_card_le {d B : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (hfiber : ∀ p ∈ X.P₂, (auxDistancePartners X ij p).card ≤ B) :
    (auxDistancePairsWithCurveLabel X ij).card ≤ X.P₂.card * B := by
  classical
  let fibers : PachDeZeeuw.Algebraic.Point2 → Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) := fun p =>
    (auxDistancePartners X ij p).image fun q => (p, q)
  have heq : auxDistancePairsWithCurveLabel X ij = X.P₂.biUnion fibers := by
    ext pq
    constructor
    · intro hpq
      have hfilter := Finset.mem_filter.mp hpq
      have hprod := Finset.mem_product.mp hfilter.1
      apply Finset.mem_biUnion.mpr
      refine ⟨pq.1, hprod.1, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨pq.2, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨hprod.2, hfilter.2⟩
    · intro hpq
      rcases Finset.mem_biUnion.mp hpq with ⟨p, hp, hpq⟩
      rcases Finset.mem_image.mp hpq with ⟨q, hq, hpq⟩
      have hfilter := Finset.mem_filter.mp hq
      subst hpq
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨hp, hfilter.1⟩, hfilter.2⟩
  rw [heq]
  apply Finset.card_biUnion_le_card_mul
  intro p hp
  calc
    (fibers p).card ≤ (auxDistancePartners X ij p).card :=
      Finset.card_image_le
    _ ≤ B := hfiber p hp


private theorem inline_Esgk_AuxiliaryIncidenceDeletion__fixedLabelIncidenceToDistancePair_injective {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    Function.Injective (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidenceToDistancePair X ij) := by
  intro incidence₁ incidence₂ hpairs
  apply Subtype.ext
  apply Prod.ext
  · have hpairs' :
        bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence₁ =
          bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence₂ :=
      congrArg Subtype.val hpairs
    let z₁ := bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePoint X ij incidence₁
    let z₂ := bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePoint X ij incidence₂
    have hencode₁ :
        encodedAuxPoint (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence₁) =
          incidence₁.1.1 :=
      encodedAuxPoint_auxPointPreimage X z₁
    have hencode₂ :
        encodedAuxPoint (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidencePair X ij incidence₂) =
          incidence₂.1.1 :=
      encodedAuxPoint_auxPointPreimage X z₂
    rw [← hencode₁, ← hencode₂, hpairs']
  · exact
      (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_label_eq X ij incidence₁.property).trans
        (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidence_label_eq X ij incidence₂.property).symm


theorem auxIncidencesWithCurveLabel_card_le_distancePairs {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    (auxIncidencesWithCurveLabel X ij).card ≤
      (auxDistancePairsWithCurveLabel X ij).card := by
  classical
  simpa using Fintype.card_le_of_injective
    (bundle_Esgk_AuxiliaryIncidenceDeletion_fixedLabelIncidenceToDistancePair X ij)
    (inline_Esgk_AuxiliaryIncidenceDeletion__fixedLabelIncidenceToDistancePair_injective X ij)


theorem auxIncidencesWithCurveLabel_card_le_of_distancePartners {d B : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁)
    (hfiber : ∀ p ∈ X.P₂, (auxDistancePartners X ij p).card ≤ B) :
    (auxIncidencesWithCurveLabel X ij).card ≤ X.P₂.card * B :=
  (auxIncidencesWithCurveLabel_card_le_distancePairs X ij).trans
    (auxDistancePairsWithCurveLabel_card_le X ij hfiber)


theorem auxIncidencesWithCurveLabel_card_le_degree_of_distancePartners
    {d B : ℕ} (X : PreparedBipartiteInput d)
    (ij : X.P₁ × X.P₁)
    (hfiber :
      ∀ p ∈ X.P₂, (auxDistancePartners X ij p).card ≤ B * d) :
    (auxIncidencesWithCurveLabel X ij).card ≤ B * d * X.P₂.card := by
  calc
    (auxIncidencesWithCurveLabel X ij).card ≤ X.P₂.card * (B * d) :=
      auxIncidencesWithCurveLabel_card_le_of_distancePartners X ij hfiber
    _ = B * d * X.P₂.card := by ring


theorem auxIncidencesWithCurveLabel_card_le_of_sharpCircleFiberBound
    (hsharp : SharpAuxiliaryCircleFiberBoundStatement)
    {d : ℕ} (X : PreparedBipartiteInput d)
    (ij : X.P₁ × X.P₁) :
    (auxIncidencesWithCurveLabel X ij).card ≤ 2 * d * X.P₂.card :=
  auxIncidencesWithCurveLabel_card_le_degree_of_distancePartners
    X ij (fun p hp => hsharp d X ij p hp)


namespace AuxiliaryIncidenceDeletionCertificate


end AuxiliaryIncidenceDeletionCertificate


private theorem inline_Esgk_AuxiliaryIncidenceDeletion__auxIncidencesOverCurveLabels_eq_biUnion {d : ℕ}
    (X : PreparedBipartiteInput d) (labels : Finset (X.P₁ × X.P₁)) :
    auxIncidencesOverCurveLabels X labels =
      bundle_Esgk_AuxiliaryIncidenceDeletion_auxIncidenceFiberUnion X labels := by
  classical
  ext incidence
  simp only [auxIncidencesOverCurveLabels, bundle_Esgk_AuxiliaryIncidenceDeletion_auxIncidenceFiberUnion,
    auxIncidencesWithCurveLabel, Finset.mem_filter, Finset.mem_biUnion]
  constructor
  · intro h
    exact ⟨incidence.2, h.2, h.1, rfl⟩
  · rintro ⟨ij, hij, haux, hlabel⟩
    exact ⟨haux, hlabel.symm ▸ hij⟩


theorem auxIncidencesOverCurveLabels_card_le {d B : ℕ}
    (X : PreparedBipartiteInput d) (labels : Finset (X.P₁ × X.P₁))
    (hfiber :
      ∀ ij ∈ labels, (auxIncidencesWithCurveLabel X ij).card ≤ B) :
    (auxIncidencesOverCurveLabels X labels).card ≤ labels.card * B := by
  classical
  rw [inline_Esgk_AuxiliaryIncidenceDeletion__auxIncidencesOverCurveLabels_eq_biUnion]
  unfold bundle_Esgk_AuxiliaryIncidenceDeletion_auxIncidenceFiberUnion
  exact Finset.card_biUnion_le_card_mul labels
    (auxIncidencesWithCurveLabel X) B hfiber


end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero
    {G : PlanePoly} (hG : G ≠ 0) :
    MvPolynomial.homogeneousComponent G.totalDegree G ≠ 0 := by
  have hsupp : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  have hsup := Finset.sup_mem_of_nonempty
    (f := fun d : Fin 2 →₀ ℕ => d.sum fun _ e => e) hsupp
  rw [← MvPolynomial.totalDegree] at hsup
  rcases hsup with ⟨d, hd, hdegree⟩
  rw [← MvPolynomial.support_nonempty]
  refine ⟨d, ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_homogeneousComponent]
  have hdegree' : Finsupp.degree d = G.totalDegree := by
    simpa [Finsupp.degree_apply, Finsupp.sum] using hdegree
  simp only [hdegree', ↓reduceIte]
  exact MvPolynomial.mem_support_iff.mp hd

 
theorem realPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    realPlaneInfinityRestriction G ≠ 0 := by
  let q : MvPolynomial (Fin 2) ℝ :=
    (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1))
      (MvPolynomial.homogeneousComponent G.totalDegree G)
  have hqhom : q.IsHomogeneous G.totalDegree := by
    exact
      (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).rename_isHomogeneous
  have hdehom : MvPolynomial.aeval ![Polynomial.X, 1] q =
      realPlaneInfinityRestriction G := by
    dsimp only [q]
    rw [MvPolynomial.renameEquiv_apply, MvPolynomial.aeval_rename]
    change (MvPolynomial.aeval (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)))
        (MvPolynomial.homogeneousComponent G.totalDegree G) =
      (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X])
        (MvPolynomial.homogeneousComponent G.totalDegree G)
    have hvec : (![(Polynomial.X : Polynomial ℝ), 1] ∘
        (Equiv.swap (0 : Fin 2) 1)) = ![(1 : Polynomial ℝ), Polynomial.X] := by
      funext i
      fin_cases i <;> simp
    rw [hvec]
  intro hzero
  have hqzero : q = 0 := by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hqhom hdehom, hzero]
    simp
  apply inline_Esgk_PlaneCircularLocalOrderDegree__homogeneousComponent_totalDegree_ne_zero hG
  exact (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) 1)).injective
    (by simpa only [map_zero] using hqzero)

 
theorem complexPlaneInfinityRestriction_ne_zero {G : PlanePoly} (hG : G ≠ 0) :
    complexPlaneInfinityRestriction G ≠ 0 := by
  exact (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr
    (realPlaneInfinityRestriction_ne_zero hG)

 
theorem realPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (realPlaneInfinityRestriction G).natDegree ≤ G.totalDegree := by
  change (MvPolynomial.aeval ![(1 : Polynomial ℝ), Polynomial.X]
    (MvPolynomial.homogeneousComponent G.totalDegree G)).natDegree ≤ G.totalDegree
  simpa using MvPolynomial.aeval_natDegree_le
    (m := G.totalDegree) (n := 1)
    (MvPolynomial.homogeneousComponent G.totalDegree G)
    (MvPolynomial.homogeneousComponent_isHomogeneous G.totalDegree G).totalDegree_le
    ![(1 : Polynomial ℝ), Polynomial.X]
    (fun i ↦ by fin_cases i <;> simp)

 
theorem complexPlaneInfinityRestriction_natDegree_le (G : PlanePoly) :
    (complexPlaneInfinityRestriction G).natDegree ≤ G.totalDegree :=
  Polynomial.natDegree_map_le.trans (realPlaneInfinityRestriction_natDegree_le G)


theorem projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding (p : PlanePoly) :
    projectiveInfinityRestriction (realPlanePolynomialProjectiveEmbedding p) =
      (realPlaneOneXRestriction p).map Complex.ofRealHom := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
        complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
        realPlaneOneXRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveInfinityRestriction, realPlanePolynomialProjectiveEmbedding,
          complexPlanePolynomialEmbedding, realToComplexPlanePolynomial,
          realPlaneOneXRestriction]


theorem projectiveInfinityRestriction_planeHomogenization (D : ℕ) (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization D G) =
      (realPlaneOneXRestriction (MvPolynomial.homogeneousComponent D G)).map
        Complex.ofRealHom := by
  rw [planeHomogenization, map_sum, Finset.sum_eq_single D]
  · simp [planeHomogenizedLayer,
      projectiveInfinityRestriction_realPlanePolynomialProjectiveEmbedding]
  · intro d hd hdD
    have hdle : d ≤ D := by
      simpa only [Finset.mem_range, Nat.lt_add_one_iff] using hd
    have hdlt : d < D := lt_of_le_of_ne hdle hdD
    have hpow : D - d ≠ 0 := Nat.sub_ne_zero_of_lt hdlt
    simp [planeHomogenizedLayer, projectiveInfinityRestriction, projectivePlaneZ, hpow]
  · simp

 
theorem projectiveInfinityRestriction_planeHomogenization_totalDegree (G : PlanePoly) :
    projectiveInfinityRestriction (planeHomogenization G.totalDegree G) =
      complexPlaneInfinityRestriction G := by
  exact projectiveInfinityRestriction_planeHomogenization G.totalDegree G


theorem chartInfinityRestriction_coeff (p : CircularChartPoly) (n : ℕ) :
    (chartInfinityRestriction p).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p := by
  change (Polynomial.map
    (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
    ((MvPolynomial.finSuccEquiv ℂ 1) p)).coeff n =
      MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  rw [Polynomial.coeff_map]
  change MvPolynomial.coeff 0 (((MvPolynomial.finSuccEquiv ℂ 1) p).coeff n) =
    MvPolynomial.coeff (Finsupp.cons n (0 : Fin 1 →₀ ℕ)) p
  exact MvPolynomial.finSuccEquiv_coeff_coeff 0 p n

@[simp]
theorem chartInfinityRestriction_C (c : ℂ) :
    chartInfinityRestriction (MvPolynomial.C c) = Polynomial.C c := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.C c)) = Polynomial.C c
  rw [MvPolynomial.finSuccEquiv_apply]
  simp

@[simp]
theorem chartInfinityRestriction_circularChartU :
    chartInfinityRestriction circularChartU = Polynomial.X := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 0)) = Polynomial.X
  rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]

@[simp]
theorem chartInfinityRestriction_circularChartZ :
    chartInfinityRestriction circularChartZ = 0 := by
  change Polynomial.map
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 1) ℂ →+* ℂ)
      ((MvPolynomial.finSuccEquiv ℂ 1) (MvPolynomial.X 1)) = 0
  rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, MvPolynomial.finSuccEquiv_X_succ]
  simp


theorem chartInfinityRestriction_projectiveCircularChart
    (c : ℂ) (P : ProjectivePlanePoly) :
    chartInfinityRestriction (projectiveCircularChart c P) =
      (projectiveInfinityRestriction P).comp (Polynomial.X + Polynomial.C c) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart, projectiveInfinityRestriction]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, projectiveInfinityRestriction, add_comm]


theorem chartInfinityRestriction_projectiveCircularChart_planeHomogenization
    (c : ℂ) (G : PlanePoly) :
    chartInfinityRestriction
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c) := by
  rw [chartInfinityRestriction_projectiveCircularChart,
    projectiveInfinityRestriction_planeHomogenization_totalDegree]


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    (c : ℂ) (F : CircularChartPoly) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hrestrict :
      chartInfinityRestriction F = p.comp (Polynomial.X + Polynomial.C c)) :
    (MvPolynomial.localOrder F).toNat ≤ p.rootMultiplicity c := by
  let q := p.comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := Polynomial.comp_X_add_C_ne_zero_iff.mpr hp
  have hcoeffq : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hcoeff :
      MvPolynomial.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict]
    exact hcoeffq
  have hcoeffSeries :
      MvPowerSeries.coeff
        (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ))
        (F : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have hdegree :
      Finsupp.degree (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) =
        q.natTrailingDegree := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change q.natTrailingDegree +
      (Finsupp.cons q.natTrailingDegree (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ =
        q.natTrailingDegree
    rw [Finsupp.cons_succ]
    simp
  have horder : MvPolynomial.localOrder F ≤ (q.natTrailingDegree : ℕ∞) := by
    simpa [MvPolynomial.localOrder, hdegree] using
      (MvPowerSeries.order_le hcoeffSeries)
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  exact ENat.toNat_le_of_le_coe horder


theorem planeCircularLocalOrder_le_rootMultiplicity
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0) :
    planeCircularLocalOrder c G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity c := by
  exact inline_Esgk_PlaneCircularLocalOrderDegree__localOrder_toNat_le_rootMultiplicity_of_chartInfinityRestriction_eq
    c (projectiveCircularChart c (planeHomogenization G.totalDegree G))
    (complexPlaneInfinityRestriction G) (complexPlaneInfinityRestriction_ne_zero hG)
    (chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G)


private theorem inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne
    {R : Type*} [DecidableEq R] {a b : R} (hab : a ≠ b) (s : Multiset R) :
    s.count a + s.count b ≤ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x s ih =>
      by_cases hxa : x = a
      · subst x
        simp only [Multiset.card_cons, Multiset.count_cons, if_neg (Ne.symm hab), add_zero,
          if_true]
        omega
      · by_cases hxb : x = b
        · subst x
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hab, add_zero, if_true]
          omega
        · have hax : a ≠ x := Ne.symm hxa
          have hbx : b ≠ x := Ne.symm hxb
          simp only [Multiset.card_cons, Multiset.count_cons, if_neg hax,
            if_neg hbx, add_zero]
          omega

 
theorem Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
    {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (p : Polynomial R) {a b : R} (hab : a ≠ b) :
    p.rootMultiplicity a + p.rootMultiplicity b ≤ p.natDegree := by
  rw [← Polynomial.count_roots p, ← Polynomial.count_roots p]
  exact (inline_Esgk_PlaneCircularLocalOrderDegree__multiset_count_add_count_le_card_of_ne hab p.roots).trans
    (Polynomial.card_roots' p)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace PachDeZeeuw.Algebraic

open MvPolynomial

 
theorem one_le_totalDegree_of_pderiv_ne_zero
    (p : PlanePoly) (i : Fin 2) (hpartial : pderiv i p ≠ 0) :
    1 ≤ p.totalDegree := by
  have hcoordinateDegree : MvPolynomial.degreeOf i p ≠ 0 := by
    intro hzero
    apply hpartial
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
    exact not_not_intro hzero
  rw [Nat.one_le_iff_ne_zero]
  intro htotalDegree
  apply hcoordinateDegree
  exact Nat.eq_zero_of_le_zero
    ((MvPolynomial.degreeOf_le_totalDegree p i).trans_eq htotalDegree)


theorem singularPointSet_ncard_le_four_mul_degree_sq_of_shear
    (p : PlanePoly) (d : ℕ) (s : ℝ)
    (hirreducible : Irreducible (shearPoly s p))
    (hdegree : (shearPoly s p).totalDegree ≤ d)
    (hpartial : pderiv (1 : Fin 2) (shearPoly s p) ≠ 0)
    (hinjective : Set.InjOn
      (fun z : PachDeZeeuw.Algebraic.Point2 ↦
        coeffCoord
          (swapPoint (chartEquiv.symm (shearPoint s (chartEquiv z)))))
      (SingularPointSet p)) :
    (SingularPointSet p).ncard ≤ 4 * d ^ 2 := by
  let h : PlanePoly := shearPoly s p
  let q : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h
  have hqirreducible : Irreducible q := by
    dsimp [q]
    exact hirreducible.map
      (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toRingEquiv
  have hrename :
      pderiv (0 : Fin 2) q =
        MvPolynomial.rename (Equiv.swap 0 1) (pderiv (1 : Fin 2) h) := by
    dsimp [q]
    simpa using
      (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective
        (x := (1 : Fin 2)) (p := h))
  have hqpartial : pderiv (0 : Fin 2) q ≠ 0 := by
    rw [hrename]
    have hinjectiveRename :=
      (MvPolynomial.renameEquiv ℝ
        (Equiv.swap (0 : Fin 2) (1 : Fin 2))).injective
    exact hinjectiveRename.ne (by simpa [h] using hpartial)
  have hresultant : ResultantCoeff q (pderiv (0 : Fin 2) q) ≠ 0 :=
    resultantCoeff_pderiv_zero_ne q hqirreducible hqpartial
  have hpositive : 0 < (Curry0 q).natDegree :=
    curry0_natDegree_pos_of_pderiv_zero_ne q hqpartial
  have hmapsTo : ∀ z ∈ SingularPointSet p,
      coeffCoord
          (swapPoint (chartEquiv.symm (shearPoint s (chartEquiv z)))) ∈
        CoeffRootSet (ResultantCoeff q (pderiv (0 : Fin 2) q)) := by
    intro z hz
    have hsingularShear :
        chartEquiv.symm (shearPoint s (chartEquiv z)) ∈ SingularPointSet h := by
      simpa [h] using singularPoint_shearPoint s p hz
    have hsingularSwap :
        swapPoint (chartEquiv.symm (shearPoint s (chartEquiv z))) ∈
          SingularPointSet q := by
      simpa [q] using singularPoint_swap h hsingularShear
    exact resultant_vanishes_at_common_zero_of_first_positive q
      (pderiv (0 : Fin 2) q) hpositive
      ⟨hsingularSwap.1.1, hsingularSwap.1.2⟩
  have hqdegree : q.totalDegree ≤ d := by
    dsimp [q]
    change ((MvPolynomial.renameEquiv ℝ
      (Equiv.swap (0 : Fin 2) (1 : Fin 2))) h).totalDegree ≤ d
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact hdegree
  have hpartialDegree : (pderiv (0 : Fin 2) q).totalDegree ≤ d :=
    (totalDegree_pderiv_le q (0 : Fin 2)).trans hqdegree
  calc
    (SingularPointSet p).ncard ≤
        (CoeffRootSet (ResultantCoeff q (pderiv (0 : Fin 2) q))).ncard :=
      Set.ncard_le_ncard_of_injOn _ hmapsTo hinjective
        (finite_coeff_roots_of_ne_zero _ hresultant)
    _ ≤ MvPolynomial.degreeOf (0 : Fin 1)
        (ResultantCoeff q (pderiv (0 : Fin 2) q)) :=
      ncard_coeff_roots_le_degreeOf _ hresultant
    _ ≤ (d + d) ^ 2 :=
      degreeOf_resultant_le q (pderiv (0 : Fin 2) q) hqdegree hpartialDegree
    _ = 4 * d ^ 2 := by ring


theorem singularPointSet_ncard_le_four_mul_degree_sq
    (p : PlanePoly) (d : ℕ)
    (hirreducible : Irreducible p)
    (hdegree : p.totalDegree ≤ d)
    (hpositive : 1 ≤ p.totalDegree) :
    (SingularPointSet p).ncard ≤ 4 * d ^ 2 := by
  classical
  have hfinite : (SingularPointSet p).Finite := by
    rcases irreducible_has_nonzero_partial p hirreducible with hpartial | hpartial
    · exact (finite_singularities_of_irreducible_bound
        p hirreducible hdegree hpartial).1
    · exact (finite_singularities_of_irreducible_bound
        p hirreducible hdegree hpartial).1
  let P : Finset (ℝ × ℝ) := hfinite.toFinset.image chartEquiv
  have hfamilyIrreducible :
      ∀ h ∈ ({p} : Finset PlanePoly), Irreducible h := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hirreducible
  have hfamilyDegree :
      ∀ h ∈ ({p} : Finset PlanePoly), h.totalDegree ≤ d := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hdegree
  have hfamilyPositive :
      ∀ h ∈ ({p} : Finset PlanePoly), 1 ≤ h.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hpositive
  obtain ⟨s, hpartialAll, hdegreeAll, hirreducibleAll, hinjectiveShear⟩ :=
    exists_good_shear ({p} : Finset PlanePoly) P d
      hfamilyIrreducible hfamilyDegree hfamilyPositive
  have hpmem : p ∈ ({p} : Finset PlanePoly) := Finset.mem_singleton_self p
  have hpartialShear : pderiv (1 : Fin 2) (shearPoly s p) ≠ 0 :=
    hpartialAll p hpmem
  have hdegreeShear : (shearPoly s p).totalDegree ≤ d :=
    hdegreeAll p hpmem
  have hirreducibleShear : Irreducible (shearPoly s p) :=
    hirreducibleAll p hpmem
  have hinjectiveProjected : Set.InjOn
      (fun z : PachDeZeeuw.Algebraic.Point2 ↦
        coeffCoord
          (swapPoint (chartEquiv.symm (shearPoint s (chartEquiv z)))))
      (SingularPointSet p) := by
    intro z hz w hw hequal
    have hzP : chartEquiv z ∈ P := by
      exact Finset.mem_image.mpr ⟨z, hfinite.mem_toFinset.mpr hz, rfl⟩
    have hwP : chartEquiv w ∈ P := by
      exact Finset.mem_image.mpr ⟨w, hfinite.mem_toFinset.mpr hw, rfl⟩
    have hequalFirst :
        (shearPoint s (chartEquiv z)).1 =
          (shearPoint s (chartEquiv w)).1 := by
      simpa [coeffCoord, swapPoint, mkPoint2] using hequal
    exact chartEquiv.injective (hinjectiveShear hzP hwP hequalFirst)
  exact singularPointSet_ncard_le_four_mul_degree_sq_of_shear
    p d s hirreducibleShear hdegreeShear hpartialShear hinjectiveProjected


theorem singularPointSet_ncard_le_four_mul_degree_sq_of_irreducible
    (p : PlanePoly) (d : ℕ)
    (hirreducible : Irreducible p)
    (hdegree : p.totalDegree ≤ d) :
    (SingularPointSet p).ncard ≤ 4 * d ^ 2 := by
  rcases irreducible_has_nonzero_partial p hirreducible with hpartial | hpartial
  · exact singularPointSet_ncard_le_four_mul_degree_sq p d hirreducible hdegree
      (one_le_totalDegree_of_pderiv_ne_zero p (0 : Fin 2) hpartial)
  · exact singularPointSet_ncard_le_four_mul_degree_sq p d hirreducible hdegree
      (one_le_totalDegree_of_pderiv_ne_zero p (1 : Fin 2) hpartial)

end PachDeZeeuw.Algebraic
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem sharp_finite_common_zero_count
    (p q : PlanePoly) (S : Finset (Fin 2 → ℝ))
    (hirr : Irreducible p)
    (hpos : 1 ≤ p.totalDegree)
    (hnot : ¬ p ∣ q)
    (hzero : ∀ z ∈ S, MvPolynomial.eval z p = 0 ∧ MvPolynomial.eval z q = 0) :
    S.card ≤ p.totalDegree * q.totalDegree := by
  let toPoint : (Fin 2 → ℝ) → PachDeZeeuw.Algebraic.Point2 := fun z ↦ WithLp.toLp 2 z
  let P : Finset (ℝ × ℝ) := S.image (fun z ↦ chartEquiv (toPoint z))
  have hfamilyIrreducible :
      ∀ h ∈ ({p} : Finset PlanePoly), Irreducible h := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hirr
  have hfamilyDegree :
      ∀ h ∈ ({p} : Finset PlanePoly), h.totalDegree ≤ p.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact le_rfl
  have hfamilyPositive :
      ∀ h ∈ ({p} : Finset PlanePoly), 1 ≤ h.totalDegree := by
    intro h hh
    rw [Finset.mem_singleton] at hh
    subst h
    exact hpos
  obtain ⟨s, hpderiv, hdegree, hirrShear, hseparate⟩ :=
    exists_good_shear ({p} : Finset PlanePoly) P p.totalDegree
      hfamilyIrreducible hfamilyDegree hfamilyPositive
  have hpmem : p ∈ ({p} : Finset PlanePoly) := Finset.mem_singleton_self p
  have hpderiv : pderiv (1 : Fin 2) (shearPoly s p) ≠ 0 := hpderiv p hpmem
  have hdegree : (shearPoly s p).totalDegree ≤ p.totalDegree := hdegree p hpmem
  have hirrShear : Irreducible (shearPoly s p) := hirrShear p hpmem
  let swap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let p' : PlanePoly := MvPolynomial.rename swap (shearPoly s p)
  let q' : PlanePoly := MvPolynomial.rename swap (shearPoly s q)
  let phi : (Fin 2 → ℝ) → (Fin 2 → ℝ) := fun z ↦
    fun i ↦ swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) i
  let T : Finset (Fin 2 → ℝ) := S.image phi
  have hphi : Set.InjOn phi (S : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    have hswap :
        swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint z)))) =
          swapPoint (chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))) := by
      ext i
      exact congrFun hzw i
    have hshear :
        chartEquiv.symm (shearPoint s (chartEquiv (toPoint z))) =
          chartEquiv.symm (shearPoint s (chartEquiv (toPoint w))) :=
      swapPoint_injective hswap
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z))).1 =
          (shearPoint s (chartEquiv (toPoint w))).1 := by
      have hpair' := congrArg chartEquiv hshear
      exact congrArg Prod.fst hpair'
    have hzP : chartEquiv (toPoint z) ∈ P :=
      Finset.mem_image.mpr ⟨z, hz, rfl⟩
    have hwP : chartEquiv (toPoint w) ∈ P :=
      Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hpair : chartEquiv (toPoint z) = chartEquiv (toPoint w) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z = toPoint w := chartEquiv.injective hpair
    funext i
    have hi := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
    simpa [toPoint] using hi
  have hTcard : T.card = S.card := by
    exact Finset.card_image_iff.mpr hphi
  have hzero' :
      ∀ z ∈ T, MvPolynomial.eval z p' = 0 ∧ MvPolynomial.eval z q' = 0 := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    have hwp : MvPolynomial.eval w p = 0 := (hzero w hw).1
    have hwq : MvPolynomial.eval w q = 0 := (hzero w hw).2
    have hshearPoint := chartEquiv.symm (shearPoint s (chartEquiv (toPoint w)))
    constructor
    · rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwp
    · rw [show q' = MvPolynomial.rename swap (shearPoly s q) by rfl]
      rw [eval_rename_swap_swapPoint]
      rw [eval_shearPoly_shearPoint_chart]
      simpa [toPoint] using hwq
  have hpartial' : pderiv (0 : Fin 2) p' ≠ 0 := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    have hrename :
        pderiv (0 : Fin 2) (MvPolynomial.rename swap (shearPoly s p)) =
          MvPolynomial.rename swap (pderiv (1 : Fin 2) (shearPoly s p)) := by
      simpa [swap] using
        (MvPolynomial.pderiv_rename swap.injective (x := (1 : Fin 2))
          (p := shearPoly s p))
    rw [hrename]
    exact (MvPolynomial.renameEquiv ℝ swap).injective.ne hpderiv
  have hpdegree' : 0 < (headCurry p').natDegree :=
    curry0_natDegree_pos_of_pderiv_zero_ne p' hpartial'
  have hirr' : Irreducible p' := by
    rw [show p' = MvPolynomial.rename swap (shearPoly s p) by rfl]
    exact hirrShear.map (MvPolynomial.renameEquiv ℝ swap).toRingEquiv
  have hnot' : ¬ p' ∣ q' := by
    intro hdiv
    change MvPolynomial.rename swap (shearPoly s p) ∣
      MvPolynomial.rename swap (shearPoly s q) at hdiv
    rw [← MvPolynomial.renameEquiv_apply, ← MvPolynomial.renameEquiv_apply] at hdiv
    have hdivShear : shearPoly s p ∣ shearPoly s q := by
      have hdiv' := map_dvd (MvPolynomial.renameEquiv ℝ swap).symm hdiv
      simpa only [AlgEquiv.symm_apply_apply] using hdiv'
    have hdivAlg : shearAlgEquiv s p ∣ shearAlgEquiv s q := by
      rw [shearAlgEquiv_apply, shearAlgEquiv_apply]
      exact hdivShear
    have hdivOrig := map_dvd (shearAlgEquiv s).symm hdivAlg
    exact hnot (by simpa only [AlgEquiv.symm_apply_apply] using hdivOrig)
  have hresultant : headResultant p' q' ≠ 0 :=
    headResultant_ne_zero_of_irreducible_not_dvd p' q' hpdegree' hirr' hnot'
  have hprojection : Set.InjOn (fun z : Fin 2 → ℝ ↦ z 1) (T : Set (Fin 2 → ℝ)) := by
    intro z hz w hw hzw
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hw
    have hi := hzw
    have hfirst :
        (shearPoint s (chartEquiv (toPoint z₀))).1 =
          (shearPoint s (chartEquiv (toPoint w₀))).1 := by
      simpa [phi, swapPoint, mkPoint2] using hi
    have hzP : chartEquiv (toPoint z₀) ∈ P :=
      Finset.mem_image.mpr ⟨z₀, hz₀, rfl⟩
    have hwP : chartEquiv (toPoint w₀) ∈ P :=
      Finset.mem_image.mpr ⟨w₀, hw₀, rfl⟩
    have hpair : chartEquiv (toPoint z₀) = chartEquiv (toPoint w₀) :=
      hseparate hzP hwP hfirst
    have hpoint : toPoint z₀ = toPoint w₀ := chartEquiv.injective hpair
    have hzw₀ : z₀ = w₀ := by
      funext i
      have hj := congrArg (fun x : PachDeZeeuw.Algebraic.Point2 ↦ x i) hpoint
      simpa [toPoint] using hj
    subst w₀
    rfl
  have hbound := common_zero_finset_card_le_totalDegree_mul
    p' q' T hpdegree' hresultant hprojection hzero'
  have hpdegreeBound : p'.totalDegree ≤ p.totalDegree := by
    dsimp [p']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s p)).totalDegree ≤ p.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact hdegree
  have hqdegreeBound : q'.totalDegree ≤ q.totalDegree := by
    dsimp [q']
    change ((MvPolynomial.renameEquiv ℝ swap) (shearPoly s q)).totalDegree ≤ q.totalDegree
    rw [MvPolynomial.totalDegree_renameEquiv]
    exact (shearPoly_totalDegree_le s q)
  calc
    S.card = T.card := hTcard.symm
    _ ≤ p'.totalDegree * q'.totalDegree := hbound
    _ ≤ p.totalDegree * q.totalDegree := Nat.mul_le_mul hpdegreeBound hqdegreeBound

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw PachDeZeeuw.Algebraic


theorem preparedSecondCurve_isAlgebraicBoundedDegreeCurve {d : ℕ}
    (X : PreparedBipartiteInput d) :
    PachDeZeeuw.Algebraic.PlaneCurve.IsBoundedDegreeCurve d X.C₂ := by
  refine ⟨preparedSecondCurvePolynomial X,
    preparedSecondCurvePolynomial_ne_zero X,
    preparedSecondCurvePolynomial_totalDegree_le X, ?_⟩
  simpa [PlaneCurveZeroSet] using preparedSecondCurvePolynomial_zeroSet X


theorem preparedSecondCurve_circle_not_subset {d : ℕ}
    (X : PreparedBipartiteInput d) (center : X.P₁) {r : ℝ} (hr : 0 < r) :
    ¬ Metric.sphere (center : _root_.Point2) r ⊆
      PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := by
  intro hsubsetZero
  have hsubset : Metric.sphere (center : _root_.Point2) r ⊆ X.C₂ := by
    rw [preparedSecondCurvePolynomial_zeroSet X]
    exact hsubsetZero
  have hnotNoCommon :
      ¬ NoCommonCurveComponent
        (Metric.sphere (center : _root_.Point2) r) X.C₂ := by
    intro hnoCommon
    rcases bezout
        (circleEquationPolynomial (center : _root_.Point2) r).totalDegree d with
      ⟨_bound, _hboundPos, hbezout⟩
    have hfinite := (hbezout
      (Metric.sphere (center : _root_.Point2) r) X.C₂
      (sphere_isBoundedDegreeCurve (center : _root_.Point2) hr)
      (preparedSecondCurve_isAlgebraicBoundedDegreeCurve X) hnoCommon).1
    have hsphereFinite :
        (Metric.sphere (center : _root_.Point2) r).Finite := by
      simpa [Set.inter_eq_left.mpr hsubset] using hfinite
    exact sphere_infinite (center : _root_.Point2) hr hsphereFinite
  have hcomponent : ∃ e : ℕ, ∃ C : Set _root_.Point2,
      PlaneCurve.IsIrreducibleCurve e C ∧ C.Infinite ∧
        C ⊆ Metric.sphere (center : _root_.Point2) r ∧ C ⊆ X.C₂ := by
    exact Classical.not_not.mp hnotNoCommon
  rcases hcomponent with ⟨_e, C, hC, hCinfinite, hCsphere, hCcarrier⟩
  rcases hC with ⟨q, _hq, _hqdeg, hqirreducible, hCzero⟩
  have hCzero' : C = PlaneCurveZeroSet q := by
    simpa [PlaneCurveZeroSet] using hCzero
  have hqinfinite : (PlaneCurveZeroSet q).Infinite := by
    simpa [← hCzero'] using hCinfinite
  have hqsubset :
      PlaneCurveZeroSet q ⊆ PlaneCurveZeroSet
        (preparedSecondCurvePolynomial X) := by
    rw [← hCzero', ← preparedSecondCurvePolynomial_zeroSet X]
    exact hCcarrier
  have hzeroSets :
      PlaneCurveZeroSet q = PlaneCurveZeroSet
        (preparedSecondCurvePolynomial X) :=
    zeroSet_eq_of_irreducible_of_infinite_subset hqirreducible
      (preparedSecondCurvePolynomial_irreducible X) hqinfinite hqsubset
  have hCeq : C = X.C₂ := by
    calc
      C = PlaneCurveZeroSet q := hCzero'
      _ = PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := hzeroSets
      _ = X.C₂ := (preparedSecondCurvePolynomial_zeroSet X).symm
  have hcarrierSubset :
      X.C₂ ⊆ Metric.sphere (center : _root_.Point2) r := by
    rw [← hCeq]
    exact hCsphere
  have hcarrierEq :
      X.C₂ = Metric.sphere (center : _root_.Point2) r :=
    Set.Subset.antisymm hcarrierSubset hsubset
  have hcenterSet :
      (center : _root_.Point2) ∈ (X.P₁ : Set _root_.Point2) := by
    exact center.property
  exact X.assumption31.circleCenterNotInPointSet.2
    (center : _root_.Point2) r hcarrierEq hcenterSet


theorem auxiliaryDistanceCircleNoncontainment :
    AuxiliaryDistanceCircleNoncontainmentStatement := by
  intro d X ij p hp
  exact preparedSecondCurve_circle_not_subset X ij.2
    (prepared_first_second_dist_pos X ij.1 hp)


theorem sharpAuxiliaryCircleFiberBound :
    SharpAuxiliaryCircleFiberBoundStatement :=
  sharpAuxiliaryCircleFiberBound_of_noncontainment
    auxiliaryDistanceCircleNoncontainment


theorem auxIncidencesWithCurveLabel_card_le_sharp {d : ℕ}
    (X : PreparedBipartiteInput d) (ij : X.P₁ × X.P₁) :
    (auxIncidencesWithCurveLabel X ij).card ≤ 2 * d * X.P₂.card :=
  auxIncidencesWithCurveLabel_card_le_of_sharpCircleFiberBound
    sharpAuxiliaryCircleFiberBound X ij


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

namespace IrreduciblePlanePolynomial











theorem normalizedLeftValue_eq_dist_xAxisPoint_neg
    (r : ℝ) (x : PachDeZeeuw.Algebraic.Point2) :
    normalizedLeftValue r x = dist x (xAxisPoint (-r)) ^ 2 := by
  rw [← eval_planeSquaredDistancePolynomial]
  simp [normalizedLeftValue]


theorem normalizedRightValue_eq_dist_xAxisPoint
    (r : ℝ) (x : PachDeZeeuw.Algebraic.Point2) :
    normalizedRightValue r x = dist x (xAxisPoint r) ^ 2 := by
  rw [← eval_planeSquaredDistancePolynomial]
  simp [normalizedRightValue]


theorem pairAffineIsometry_image_twoPairDistanceCommonZeroSet_subset
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂) :
    (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) ''
        twoPairDistanceCommonZeroSet C a c b d ⊆
      normalizedDistancePairCommonZeroSet
        (C.affineIsometryTransport g₁)
        (C.affineIsometryTransport g₂) r₁ r₂ := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← C.affineIsometry_image_zeroSet_eq g₁]
    exact ⟨z.1, hz.1, rfl⟩
  · rw [← C.affineIsometry_image_zeroSet_eq g₂]
    exact ⟨z.2, hz.2.1, rfl⟩
  · rw [normalizedLeftValue_eq_dist_xAxisPoint_neg,
      normalizedLeftValue_eq_dist_xAxisPoint_neg, ← hg₁a, ← hg₂b,
      g₁.dist_map, g₂.dist_map]
    exact hz.2.2.1
  · rw [normalizedRightValue_eq_dist_xAxisPoint,
      normalizedRightValue_eq_dist_xAxisPoint, ← hg₁c, ← hg₂d,
      g₁.dist_map, g₂.dist_map]
    exact hz.2.2.2
















end IrreduciblePlanePolynomial

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem localOrder_map_star {σ : Type*} (p : MvPolynomial σ ℂ) :
    localOrder (map (starRingEnd ℂ) p) = localOrder p := by
  have hcoe :
      ((map (starRingEnd ℂ) p : MvPolynomial σ ℂ) : MvPowerSeries σ ℂ) =
        MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ) := by
    ext d
    exact MvPolynomial.coeff_map (starRingEnd ℂ) p d
  rw [localOrder, localOrder, hcoe]
  apply le_antisymm
  · have h := MvPowerSeries.le_order_map (starRingEnd ℂ)
      (φ := MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ))
    have hinvolution :
        MvPowerSeries.map (starRingEnd ℂ)
            (MvPowerSeries.map (starRingEnd ℂ) (p : MvPowerSeries σ ℂ)) = p := by
      ext d
      simp
    rw [hinvolution] at h
    exact h
  · exact MvPowerSeries.le_order_map (starRingEnd ℂ)

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star (p : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (realPlanePolynomialProjectiveEmbedding p) =
      realPlanePolynomialProjectiveEmbedding p := by
  change
    MvPolynomial.map (starRingEnd ℂ)
        (MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)) =
      MvPolynomial.rename Fin.castSucc (MvPolynomial.map Complex.ofRealHom p)
  rw [MvPolynomial.map_rename, MvPolynomial.map_map]
  have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext r
    simp
  rw [hcomp]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star (D : ℕ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (planeHomogenization D G) = planeHomogenization D G := by
  simp only [planeHomogenization, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [planeHomogenizedLayer, inline_Esgk_PlaneCircularLocalOrderConjugation__realPlanePolynomialProjectiveEmbedding_map_star,
    projectivePlaneZ]

private theorem inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star (c : ℂ) (P : ProjectivePlanePoly) :
    MvPolynomial.map (starRingEnd ℂ) (projectiveCircularChart c P) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (MvPolynomial.map (starRingEnd ℂ) P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [projectiveCircularChart]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      fin_cases i <;>
        simp [projectiveCircularChart, circularChartU, circularChartZ]


theorem projectiveCircularChart_planeHomogenization_map_star (c : ℂ) (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) =
      projectiveCircularChart ((starRingEnd ℂ) c)
        (planeHomogenization G.totalDegree G) := by
  rw [inline_Esgk_PlaneCircularLocalOrderConjugation__projectiveCircularChart_map_star, inline_Esgk_PlaneCircularLocalOrderConjugation__planeHomogenization_map_star]

 
theorem projectiveCircularChartI_planeHomogenization_map_star (G : PlanePoly) :
    MvPolynomial.map (starRingEnd ℂ)
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)) =
      projectiveCircularChartJ (planeHomogenization G.totalDegree G) := by
  simpa [projectiveCircularChartI, projectiveCircularChartJ, Complex.conj_I] using
    projectiveCircularChart_planeHomogenization_map_star Complex.I G


theorem planeCircularLocalOrderI_eq_planeCircularLocalOrderJ (G : PlanePoly) :
    planeCircularLocalOrderI G = planeCircularLocalOrderJ G := by
  change
    (MvPolynomial.localOrder
        (projectiveCircularChartI (planeHomogenization G.totalDegree G))).toNat =
      (MvPolynomial.localOrder
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G))).toNat
  have h := MvPolynomial.localOrder_map_star
    (projectiveCircularChartI (planeHomogenization G.totalDegree G))
  rw [projectiveCircularChartI_planeHomogenization_map_star] at h
  exact congrArg ENat.toNat h.symm

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem planeGradientSquare_totalDegree_le
    {G : PlanePoly} {d : ℕ}
    (hpos : 0 < G.totalDegree) (hdegree : G.totalDegree ≤ d) :
    (planeGradientSquare G).totalDegree ≤ 2 * (d - 1) := by
  have h₀ : (pderiv (0 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
    totalDegree_pderiv_le_sub_one G 0 hpos
  have h₁ : (pderiv (1 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
    totalDegree_pderiv_le_sub_one G 1 hpos
  have h₀' : (pderiv (0 : Fin 2) G).totalDegree ≤ d - 1 :=
    h₀.trans (Nat.sub_le_sub_right hdegree 1)
  have h₁' : (pderiv (1 : Fin 2) G).totalDegree ≤ d - 1 :=
    h₁.trans (Nat.sub_le_sub_right hdegree 1)
  have hs₀ : ((pderiv (0 : Fin 2) G) ^ 2).totalDegree ≤ 2 * (d - 1) :=
    (MvPolynomial.totalDegree_pow _ 2).trans
      (Nat.mul_le_mul_left 2 h₀')
  have hs₁ : ((pderiv (1 : Fin 2) G) ^ 2).totalDegree ≤ 2 * (d - 1) :=
    (MvPolynomial.totalDegree_pow _ 2).trans
      (Nat.mul_le_mul_left 2 h₁')
  calc
    (planeGradientSquare G).totalDegree ≤
        max ((pderiv (0 : Fin 2) G) ^ 2).totalDegree
          ((pderiv (1 : Fin 2) G) ^ 2).totalDegree := by
      exact MvPolynomial.totalDegree_add _ _
    _ ≤ 2 * (d - 1) := max_le hs₀ hs₁

 
theorem planeGradientCutoff_forbidden_constant_at_most_one
    {G : PlanePoly} (hG : Irreducible G) {ε₁ ε₂ : ℝ}
    (h₁ : G ∣ planeGradientCutoff G ε₁)
    (h₂ : G ∣ planeGradientCutoff G ε₂) :
    ε₁ = ε₂ := by
  have hdiv : G ∣ C (ε₂ - ε₁) := by
    have hsub : G ∣ planeGradientCutoff G ε₁ - planeGradientCutoff G ε₂ :=
      dvd_sub h₁ h₂
    convert hsub using 1
    simp only [planeGradientCutoff]
    rw [map_sub]
    ring
  by_contra hne
  have hdiff : ε₂ - ε₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hunit : IsUnit (C (ε₂ - ε₁) : PlanePoly) :=
    IsUnit.map (MvPolynomial.C : ℝ →+* PlanePoly)
      (isUnit_iff_ne_zero.mpr hdiff)
  exact (not_isUnit_of_not_isUnit_dvd hG.not_isUnit hdiv) hunit

 
theorem singularPointSet_ncard_le_degree_mul_pred
    {G : PlanePoly} {d : ℕ}
    (hG : Irreducible G) (hdegree : G.totalDegree ≤ d) :
    (SingularPointSet G).ncard ≤ d * (d - 1) := by
  rcases irreducible_has_nonzero_partial G hG with hpartial | hpartial
  · have hpos : 1 ≤ G.totalDegree :=
      one_le_totalDegree_of_pderiv_ne_zero G 0 hpartial
    have hfinite : (SingularPointSet G).Finite :=
      (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
    let embedding : PachDeZeeuw.Algebraic.Point2 ↪ (Fin 2 → ℝ) :=
      ⟨fun z ↦ WithLp.equiv 2 (Fin 2 → ℝ) z,
        (WithLp.equiv 2 (Fin 2 → ℝ)).injective⟩
    let S : Finset (Fin 2 → ℝ) := hfinite.toFinset.map embedding
    have hzero : ∀ z ∈ S,
        MvPolynomial.eval z G = 0 ∧
          MvPolynomial.eval z (pderiv (0 : Fin 2) G) = 0 := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
      have hp' := hfinite.mem_toFinset.mp hp
      rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hp'
      rcases hp' with ⟨⟨hcurve, hzero₀⟩, _⟩
      constructor
      · simpa [PlaneCurveZeroSet, embedding] using hcurve
      · simpa [embedding] using hzero₀
    have hbound := sharp_finite_common_zero_count G
      (pderiv (0 : Fin 2) G) S hG hpos
      (irreducible_not_dvd_nonzero_partial G hG hpartial) hzero
    have hS : S.card = (SingularPointSet G).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfinite]
      simp [S]
    have hpartialDegree :
        (pderiv (0 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
      totalDegree_pderiv_le_sub_one G 0 (Nat.zero_lt_of_lt hpos)
    calc
      (SingularPointSet G).ncard = S.card := hS.symm
      _ ≤ G.totalDegree * (pderiv (0 : Fin 2) G).totalDegree := hbound
      _ ≤ G.totalDegree * (G.totalDegree - 1) :=
        Nat.mul_le_mul_left _ hpartialDegree
      _ ≤ d * (d - 1) := Nat.mul_le_mul hdegree
        (Nat.sub_le_sub_right hdegree 1)
  · have hpos : 1 ≤ G.totalDegree :=
      one_le_totalDegree_of_pderiv_ne_zero G 1 hpartial
    have hfinite : (SingularPointSet G).Finite :=
      (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
    let embedding : PachDeZeeuw.Algebraic.Point2 ↪ (Fin 2 → ℝ) :=
      ⟨fun z ↦ WithLp.equiv 2 (Fin 2 → ℝ) z,
        (WithLp.equiv 2 (Fin 2 → ℝ)).injective⟩
    let S : Finset (Fin 2 → ℝ) := hfinite.toFinset.map embedding
    have hzero : ∀ z ∈ S,
        MvPolynomial.eval z G = 0 ∧
          MvPolynomial.eval z (pderiv (1 : Fin 2) G) = 0 := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
      have hp' := hfinite.mem_toFinset.mp hp
      rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hp'
      rcases hp' with ⟨⟨hcurve, _⟩, hzero₁⟩
      constructor
      · simpa [PlaneCurveZeroSet, embedding] using hcurve
      · simpa [embedding] using hzero₁
    have hbound := sharp_finite_common_zero_count G
      (pderiv (1 : Fin 2) G) S hG hpos
      (irreducible_not_dvd_nonzero_partial G hG hpartial) hzero
    have hS : S.card = (SingularPointSet G).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hfinite]
      simp [S]
    have hpartialDegree :
        (pderiv (1 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
      totalDegree_pderiv_le_sub_one G 1 (Nat.zero_lt_of_lt hpos)
    calc
      (SingularPointSet G).ncard = S.card := hS.symm
      _ ≤ G.totalDegree * (pderiv (1 : Fin 2) G).totalDegree := hbound
      _ ≤ G.totalDegree * (G.totalDegree - 1) :=
        Nat.mul_le_mul_left _ hpartialDegree
      _ ≤ d * (d - 1) := Nat.mul_le_mul hdegree
        (Nat.sub_le_sub_right hdegree 1)

 
theorem planeGradientCutoffZeroSet_finite_and_ncard_le
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G)
    (hdegree : G.totalDegree ≤ d) (hpos : 1 ≤ G.totalDegree)
    (ε : ℝ) (hnot : ¬ G ∣ planeGradientCutoff G ε) :
    (planeGradientCutoffZeroSet G ε).Finite ∧
      (planeGradientCutoffZeroSet G ε).ncard ≤ 2 * d * (d - 1) := by
  have hfinite : (planeGradientCutoffZeroSet G ε).Finite := by
    apply Set.not_infinite.mp
    intro hinf
    exact hnot (dvd_of_infinite_irreducible_zeroSet_intersection hG hinf)
  let embedding : PachDeZeeuw.Algebraic.Point2 ↪ (Fin 2 → ℝ) :=
    ⟨fun z ↦ WithLp.equiv 2 (Fin 2 → ℝ) z,
      (WithLp.equiv 2 (Fin 2 → ℝ)).injective⟩
  let S : Finset (Fin 2 → ℝ) := hfinite.toFinset.map embedding
  have hzero : ∀ z ∈ S,
      MvPolynomial.eval z G = 0 ∧
        MvPolynomial.eval z (planeGradientCutoff G ε) = 0 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
    have hp' := hfinite.mem_toFinset.mp hp
    rw [planeGradientCutoffZeroSet, Set.mem_inter_iff] at hp'
    rcases hp' with ⟨hcurve, hcutoff⟩
    constructor
    · simpa [PlaneCurveZeroSet, embedding] using hcurve
    · simpa [PlaneCurveZeroSet, embedding] using hcutoff
  have hbound := sharp_finite_common_zero_count G
    (planeGradientCutoff G ε) S hG hpos hnot hzero
  have hcutoffDegree :
      (planeGradientCutoff G ε).totalDegree ≤ 2 * (d - 1) := by
    dsimp [planeGradientCutoff]
    exact (MvPolynomial.totalDegree_sub_C_le _ _).trans
      (planeGradientSquare_totalDegree_le (Nat.zero_lt_of_lt hpos) hdegree)
  have hS : S.card = (planeGradientCutoffZeroSet G ε).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    simp [S]
  refine ⟨hfinite, ?_⟩
  calc
      (planeGradientCutoffZeroSet G ε).ncard = S.card := hS.symm
      _ ≤ G.totalDegree * (planeGradientCutoff G ε).totalDegree := hbound
      _ ≤ G.totalDegree * (2 * (d - 1)) :=
        Nat.mul_le_mul_left _ hcutoffDegree
      _ ≤ d * (2 * (d - 1)) := Nat.mul_le_mul_right _ hdegree
      _ = 2 * d * (d - 1) := by ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


private theorem inline_Esgk_PlaneCurveRadialCritical__planeRadialCritical_linear_degree_le
    (a : PachDeZeeuw.Algebraic.Point2) (i : Fin 2) :
    (X i - C (a i) : PlanePoly).totalDegree ≤ 1 := by
  simpa using
    (MvPolynomial.totalDegree_sub_C_le (X i : PlanePoly) (a i))

 
theorem planeRadialCritical_totalDegree_le
    {G : PlanePoly} {a : PachDeZeeuw.Algebraic.Point2} {d : ℕ}
    (hpos : 0 < G.totalDegree) (hdegree : G.totalDegree ≤ d) :
    (planeRadialCritical G a).totalDegree ≤ d := by
  have hpartial₀ :
      (pderiv (0 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
    totalDegree_pderiv_le_sub_one G 0 hpos
  have hpartial₁ :
      (pderiv (1 : Fin 2) G).totalDegree ≤ G.totalDegree - 1 :=
    totalDegree_pderiv_le_sub_one G 1 hpos
  have hterm₀ :
      ((X 0 - C (a 0)) * pderiv (1 : Fin 2) G : PlanePoly).totalDegree ≤ d := by
    calc
      _ ≤ (X 0 - C (a 0) : PlanePoly).totalDegree +
          (pderiv (1 : Fin 2) G).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + (G.totalDegree - 1) :=
        Nat.add_le_add
          (inline_Esgk_PlaneCurveRadialCritical__planeRadialCritical_linear_degree_le a 0) hpartial₁
      _ ≤ d := by omega
  have hterm₁ :
      ((X 1 - C (a 1)) * pderiv (0 : Fin 2) G : PlanePoly).totalDegree ≤ d := by
    calc
      _ ≤ (X 1 - C (a 1) : PlanePoly).totalDegree +
          (pderiv (0 : Fin 2) G).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 + (G.totalDegree - 1) :=
        Nat.add_le_add
          (inline_Esgk_PlaneCurveRadialCritical__planeRadialCritical_linear_degree_le a 1) hpartial₀
      _ ≤ d := by omega
  have hsub := MvPolynomial.totalDegree_sub
    ((X 0 - C (a 0)) * pderiv (1 : Fin 2) G : PlanePoly)
    ((X 1 - C (a 1)) * pderiv (0 : Fin 2) G : PlanePoly)
  simpa [planeRadialCritical] using hsub.trans (max_le hterm₀ hterm₁)

 
theorem planeRadialCriticalZeroSet_finite_and_ncard_le
    {G : PlanePoly} {a : PachDeZeeuw.Algebraic.Point2} {d : ℕ}
    (hG : Irreducible G) (hpos : 0 < G.totalDegree)
    (hdegree : G.totalDegree ≤ d)
    (hnot : ¬ G ∣ planeRadialCritical G a) :
    (planeRadialCriticalZeroSet G a).Finite ∧
      (planeRadialCriticalZeroSet G a).ncard ≤ d * d := by
  have hfinite : (planeRadialCriticalZeroSet G a).Finite := by
    apply Set.not_infinite.mp
    intro hinf
    exact hnot (dvd_of_infinite_irreducible_zeroSet_intersection hG hinf)
  let embedding : PachDeZeeuw.Algebraic.Point2 ↪ (Fin 2 → ℝ) :=
    ⟨fun z ↦ WithLp.equiv 2 (Fin 2 → ℝ) z,
      (WithLp.equiv 2 (Fin 2 → ℝ)).injective⟩
  let S : Finset (Fin 2 → ℝ) := hfinite.toFinset.map embedding
  have hzero : ∀ z ∈ S,
      MvPolynomial.eval z G = 0 ∧
        MvPolynomial.eval z (planeRadialCritical G a) = 0 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
    have hp' := hfinite.mem_toFinset.mp hp
    rw [planeRadialCriticalZeroSet, Set.mem_inter_iff] at hp'
    rcases hp' with ⟨hcurve, hcritical⟩
    constructor
    · simpa [PlaneCurveZeroSet, embedding] using hcurve
    · simpa [PlaneCurveZeroSet, embedding] using hcritical
  have hbound := sharp_finite_common_zero_count G
    (planeRadialCritical G a) S hG
    (by omega : 1 ≤ G.totalDegree) hnot hzero
  have hRaDegree : (planeRadialCritical G a).totalDegree ≤ d :=
    planeRadialCritical_totalDegree_le hpos hdegree
  have hS : S.card = (planeRadialCriticalZeroSet G a).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfinite]
    simp [S]
  refine ⟨hfinite, ?_⟩
  calc
    (planeRadialCriticalZeroSet G a).ncard = S.card := hS.symm
    _ ≤ G.totalDegree * (planeRadialCritical G a).totalDegree := hbound
    _ ≤ d * d := Nat.mul_le_mul hdegree hRaDegree

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.order_sum_eq_totalDegree
    {G : PlanePoly} (hG : IsMaximallyCircular G) :
    planeCircularLocalOrderI G + planeCircularLocalOrderJ G = G.totalDegree := by
  rcases hG with ⟨hI, hJ⟩
  omega


variable {n : ℕ}


end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Filter Topology MvPolynomial
open PachDeZeeuw.Algebraic

namespace Esgk

 
theorem hasDerivAt_evalPlane (G : PlanePoly) {u v : ℝ → ℝ} {u' v' t : ℝ}
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s ↦ evalPlane G (u s, v s))
      (evalPlane (pderiv 0 G) (u t, v t) * u' +
        evalPlane (pderiv 1 G) (u t, v t) * v') t := by
  induction G using MvPolynomial.induction_on with
  | C c => simpa [evalPlane] using hasDerivAt_const t c
  | add p q hp hq =>
      convert hp.add hq using 1
      all_goals first
        | rfl
        | (funext s; simp [evalPlane])
        | (simp only [evalPlane, map_add]; ring)
  | mul_X p i hp =>
      fin_cases i
      · convert hp.mul hu using 1
        all_goals first
          | rfl
          | (funext s; simp [evalPlane])
          | (simp [evalPlane, pderiv_X]; ring)
      · convert hp.mul hv using 1
        all_goals first
          | rfl
          | (funext s; simp [evalPlane])
          | (simp [evalPlane, pderiv_X]; ring)


theorem exists_smooth_implicitGraph_of_partial1 (G : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hpartial : evalPlane (pderiv 1 G) z ≠ 0) :
    ∃ ψ : ℝ → ℝ, ψ z.1 = z.2 ∧ ContDiffAt ℝ ⊤ ψ z.1 ∧
      (∀ᶠ t in 𝓝 z.1, evalPlane G (t, ψ t) = 0) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 ↔ ψ w.1 = w.2) := by
  let : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  let : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  let hcont : ContDiffAt ℝ ⊤ (evalPlane G) z := (evalPlane_contDiff G).contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hfd : HasFDerivAt (evalPlane G) (fderiv ℝ (evalPlane G) z) z :=
    (hcont.differentiableAt hn).hasFDerivAt
  have hinr : HasFDerivAt (fun y : ℝ ↦ (z.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) z.2 := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hslice := hasDerivAt_evalPlane G (hasDerivAt_const z.2 z.1) (hasDerivAt_id z.2)
  have hslice' : HasFDerivAt (fun y : ℝ ↦ evalPlane G (z.1, y))
      (ContinuousLinearMap.toSpanSingleton ℝ (evalPlane (pderiv 1 G) z)) z.2 := by
    simpa using hslice.hasFDerivAt
  have hcomp : fderiv ℝ (evalPlane G) z ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ (evalPlane (pderiv 1 G) z) := by
    have hh : HasFDerivAt (fun y : ℝ ↦ evalPlane G (z.1, y))
        (fderiv ℝ (evalPlane G) z ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) z.2 := by
      convert hfd.comp z.2 hinr using 1
      rfl
    exact hh.unique hslice'
  have hinv :
      (fderiv ℝ (evalPlane G) z ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    apply hasFDerivAt_isInvertible_partial hfd
    rw [hcomp]
    exact toSpanSingleton_bijective_of_ne_zero _ hpartial
  refine ⟨hcont.implicitFunction hn hinv, hcont.implicitFunction_apply_self hn hinv,
    hcont.contDiffAt_implicitFunction hn hinv, ?_, ?_⟩
  · simpa only [hz] using hcont.eventually_apply_implicitFunction hn hinv
  · simpa only [hz] using hcont.eventually_apply_eq_iff_implicitFunction hn hinv


theorem planeSquaredRadius_eq_dist_sq (a : PachDeZeeuw.Algebraic.Point2) (z : ℝ × ℝ) :
    planeSquaredRadius a z = dist (mkPoint2 z.1 z.2) a ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp [planeSquaredRadius, Fin.sum_univ_two, mkPoint2, Real.dist_eq, sq_abs]

 
theorem implicitGraph_tangent_identity (G : PlanePoly) {ψ : ℝ → ℝ} {t ψ' : ℝ}
    (hψ : HasDerivAt ψ ψ' t)
    (hcurve : ∀ᶠ s in 𝓝 t, evalPlane G (s, ψ s) = 0) :
    evalPlane (pderiv 0 G) (t, ψ t) +
      evalPlane (pderiv 1 G) (t, ψ t) * ψ' = 0 := by
  have hd := hasDerivAt_evalPlane G (hasDerivAt_id t) hψ
  have hz : HasDerivAt (fun s ↦ evalPlane G (s, ψ s)) 0 t :=
    (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hcurve
  simpa using hd.unique hz


theorem hasDerivAt_planeSquaredRadius_implicitGraph (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2)
    {ψ : ℝ → ℝ} {t ψ' : ℝ} (hψ : HasDerivAt ψ ψ' t)
    (hcurve : ∀ᶠ s in 𝓝 t, evalPlane G (s, ψ s) = 0)
    (hpartial : evalPlane (pderiv 1 G) (t, ψ t) ≠ 0) :
    HasDerivAt (fun s ↦ planeSquaredRadius a (s, ψ s))
      (2 * evalPlane (planeRadialCritical G a) (t, ψ t) /
        evalPlane (pderiv 1 G) (t, ψ t)) t := by
  have ht := implicitGraph_tangent_identity G hψ hcurve
  have hd := ((hasDerivAt_id t).sub_const (a 0)).pow 2
  have he := (hψ.sub_const (a 1)).pow 2
  apply (hd.add he).congr_deriv
  have hr : evalPlane (planeRadialCritical G a) (t, ψ t) =
      (t - a 0) * evalPlane (pderiv 1 G) (t, ψ t) -
        (ψ t - a 1) * evalPlane (pderiv 0 G) (t, ψ t) := by
    simp [planeRadialCritical, evalPlane]
  rw [hr]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, id_eq, mul_one]
  field_simp [hpartial]
  linear_combination (ψ t - a 1) * ht


theorem planeSquaredRadius_const_of_radialCritical_eq_zero (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2)
    {ψ : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) (hc : IsPreconnected s)
    (hψ : DifferentiableOn ℝ ψ s) (hcurve : ∀ t ∈ s, evalPlane G (t, ψ t) = 0)
    (hpartial : ∀ t ∈ s, evalPlane (pderiv 1 G) (t, ψ t) ≠ 0)
    (hradial : ∀ t ∈ s, evalPlane (planeRadialCritical G a) (t, ψ t) = 0) :
    ∃ r : ℝ, ∀ t ∈ s, planeSquaredRadius a (t, ψ t) = r := by
  have hd : ∀ t ∈ s, HasDerivAt (fun u ↦ planeSquaredRadius a (u, ψ u)) 0 t := by
    intro t ht
    have hψt := ((hψ t ht).differentiableAt (hs.mem_nhds ht)).hasDerivAt
    have he : ∀ᶠ u in 𝓝 t, evalPlane G (u, ψ u) = 0 :=
      mem_of_superset (hs.mem_nhds ht) (fun u hu ↦ hcurve u hu)
    simpa only [hradial t ht, mul_zero, zero_div] using
      hasDerivAt_planeSquaredRadius_implicitGraph G a hψt he (hpartial t ht)
  exact hs.exists_is_const_of_deriv_eq_zero hc
    (fun t ht ↦ (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht ↦ (hd t ht).deriv)


theorem exists_radialGraphChart_of_partial1 (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hpartial : evalPlane (pderiv 1 G) z ≠ 0)
    (hradial : evalPlane (planeRadialCritical G a) z ≠ 0) :
    ∃ (ψ : ℝ → ℝ) (e : OpenPartialHomeomorph ℝ ℝ),
      ψ z.1 = z.2 ∧ ContDiffAt ℝ ⊤ ψ z.1 ∧
      (∀ᶠ t in 𝓝 z.1, evalPlane G (t, ψ t) = 0) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 ↔ ψ w.1 = w.2) ∧
      z.1 ∈ e.source ∧ (∀ t, e t = planeSquaredRadius a (t, ψ t)) := by
  obtain ⟨ψ, hψz, hψ, hcurve, hlocal⟩ :=
    exists_smooth_implicitGraph_of_partial1 G hz hpartial
  let r : ℝ → ℝ := fun t ↦ planeSquaredRadius a (t, ψ t)
  let d : ℝ := 2 * evalPlane (planeRadialCritical G a) (z.1, ψ z.1) /
    evalPlane (pderiv 1 G) (z.1, ψ z.1)
  have hp : evalPlane (pderiv 1 G) (z.1, ψ z.1) ≠ 0 := by simpa [hψz] using hpartial
  have hd : HasDerivAt r d z.1 :=
    hasDerivAt_planeSquaredRadius_implicitGraph G a
      (hψ.differentiableAt (by simp)).hasDerivAt hcurve hp
  have hd0 : d ≠ 0 := by
    dsimp [d]
    exact div_ne_zero (mul_ne_zero two_ne_zero (by simpa [hψz] using hradial)) hp
  have hr : ContDiffAt ℝ ⊤ r z.1 := by
    dsimp [r, planeSquaredRadius]
    fun_prop
  have hi := (hr.hasStrictDerivAt' hd (by simp)).hasStrictFDerivAt_equiv hd0
  refine ⟨ψ, hi.toOpenPartialHomeomorph r, hψz, hψ, hcurve, hlocal,
    hi.mem_toOpenPartialHomeomorph_source, ?_⟩
  intro t
  rfl


theorem exists_localRadialInverse_of_partial1 (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hpartial : evalPlane (pderiv 1 G) z ≠ 0)
    (hradial : evalPlane (planeRadialCritical G a) z ≠ 0) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ (planeSquaredRadius a z) = z ∧ ContinuousAt γ (planeSquaredRadius a z) ∧
      (∀ᶠ r in 𝓝 (planeSquaredRadius a z),
        evalPlane G (γ r) = 0 ∧ planeSquaredRadius a (γ r) = r) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 → γ (planeSquaredRadius a w) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ planeSquaredRadius a z ∈ U ∧ ContinuousOn γ U) := by
  obtain ⟨ψ, e, hψz, hψ, hcurve, hlocal, hsource, he⟩ :=
    exists_radialGraphChart_of_partial1 G a hz hpartial hradial
  let γ : ℝ → ℝ × ℝ := fun r ↦ (e.symm r, ψ (e.symm r))
  have hbase : e z.1 = planeSquaredRadius a z := by simpa [hψz] using he z.1
  have htend : Tendsto e.symm (𝓝 (planeSquaredRadius a z)) (𝓝 z.1) := by
    simpa only [hbase] using e.tendsto_symm hsource
  have hγbase : γ (planeSquaredRadius a z) = z := by
    dsimp [γ]
    rw [← hbase, e.left_inv hsource, hψz]
  refine ⟨γ, hγbase, ?_, ?_, ?_, ?_⟩
  · have hc := htend.prodMk_nhds (hψ.continuousAt.tendsto.comp htend)
    rw [ContinuousAt, hγbase]
    simpa only [γ, hψz, Prod.mk.eta, Function.comp_apply] using hc
  · have hr : ∀ᶠ r in 𝓝 (planeSquaredRadius a z), e (e.symm r) = r := by
      simpa only [hbase] using e.eventually_right_inverse' hsource
    filter_upwards [htend.eventually hcurve, hr] with r hc hr
    exact ⟨hc, (he (e.symm r)).symm.trans hr⟩
  · have hl :=
      (continuous_fst.continuousAt : ContinuousAt (Prod.fst : ℝ × ℝ → ℝ) z).eventually
        (e.eventually_left_inverse hsource)
    filter_upwards [hlocal, hl] with w hw hl
    intro hGw
    have hψw := hw.mp hGw
    have hrw : e w.1 = planeSquaredRadius a w := by simpa only [hψw, Prod.mk.eta] using he w.1
    dsimp [γ]
    rw [← hrw, hl, hψw]
  · obtain ⟨V, hV, hVψ⟩ : ∃ V ∈ 𝓝 z.1, ContDiffOn ℝ 0 ψ V :=
      hψ.contDiffOn le_top (by simp)
    let U : Set ℝ := e.target ∩ e.symm ⁻¹' interior V
    have hUc : ContinuousOn e.symm U := e.continuousOn_symm.mono inter_subset_left
    refine ⟨U, e.symm.isOpen_inter_preimage isOpen_interior, ?_, ?_⟩
    · constructor
      · rw [← hbase]
        exact e.map_source hsource
      · change e.symm (planeSquaredRadius a z) ∈ interior V
        rw [← hbase, e.left_inv hsource]
        exact mem_interior_iff_mem_nhds.mpr hV
    · exact hUc.prodMk ((contDiffOn_zero.mp hVψ).comp hUc
        (fun t ht ↦ interior_subset ht.2))


theorem exists_regular_implicitGraph_interval_of_partial1 (G : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hpartial : evalPlane (pderiv 1 G) z ≠ 0) :
    ∃ (ψ : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ ψ z.1 = z.2 ∧
      ContDiffOn ℝ 1 ψ (Metric.ball z.1 ε) ∧
      (∀ t ∈ Metric.ball z.1 ε, evalPlane G (t, ψ t) = 0) ∧
      (∀ t ∈ Metric.ball z.1 ε, evalPlane (pderiv 1 G) (t, ψ t) ≠ 0) := by
  obtain ⟨ψ, hψz, hψ, hcurve, _⟩ := exists_smooth_implicitGraph_of_partial1 G hz hpartial
  obtain ⟨U, hU, hUψ⟩ : ∃ U ∈ 𝓝 z.1, ContDiffOn ℝ 1 ψ U :=
    hψ.contDiffOn le_top (by simp)
  have hpcont : ContinuousAt (fun t ↦ evalPlane (pderiv 1 G) (t, ψ t)) z.1 :=
    (evalPlane_contDiff (pderiv 1 G)).continuous.continuousAt.comp
      (continuousAt_id.prodMk hψ.continuousAt)
  have hp : ∀ᶠ t in 𝓝 z.1, evalPlane (pderiv 1 G) (t, ψ t) ≠ 0 :=
    (hpcont.ne_iff_eventually_ne continuousAt_const).mp (by simpa [hψz] using hpartial)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hU (inter_mem hcurve hp))
  refine ⟨ψ, ε, hε, hψz, hUψ.mono (fun t ht ↦ (hball ht).1), ?_, ?_⟩
  · intro t ht
    exact (hball ht).2.1
  · intro t ht
    exact (hball ht).2.2

 
theorem evalPlane_pderiv_swap_zero (G : PlanePoly) (z : ℝ × ℝ) :
    evalPlane (pderiv 0 (rename (Equiv.swap 0 1) G)) z.swap =
      evalPlane (pderiv 1 G) z := by
  have he : pderiv 0 (rename (Equiv.swap 0 1) G) =
      rename (Equiv.swap 0 1) (pderiv 1 G) := by
    simpa using pderiv_rename (Equiv.swap 0 1).injective (x := (1 : Fin 2)) (p := G)
  rw [he]
  exact evalPlane_rename_swap (pderiv 1 G) z.2 z.1

 
theorem evalPlane_pderiv_swap_one (G : PlanePoly) (z : ℝ × ℝ) :
    evalPlane (pderiv 1 (rename (Equiv.swap 0 1) G)) z.swap =
      evalPlane (pderiv 0 G) z := by
  have he : pderiv 1 (rename (Equiv.swap 0 1) G) =
      rename (Equiv.swap 0 1) (pderiv 0 G) := by
    simpa using pderiv_rename (Equiv.swap 0 1).injective (x := (0 : Fin 2)) (p := G)
  rw [he]
  exact evalPlane_rename_swap (pderiv 0 G) z.2 z.1

 
theorem evalPlane_planeRadialCritical (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) (z : ℝ × ℝ) :
    evalPlane (planeRadialCritical G a) z =
      (z.1 - a 0) * evalPlane (pderiv 1 G) z -
        (z.2 - a 1) * evalPlane (pderiv 0 G) z := by
  simp [planeRadialCritical, evalPlane]

 
theorem evalPlane_radialCritical_swap (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) (z : ℝ × ℝ) :
    evalPlane (planeRadialCritical (rename (Equiv.swap 0 1) G) (swapPoint a)) z.swap =
      -evalPlane (planeRadialCritical G a) z := by
  rw [evalPlane_planeRadialCritical, evalPlane_planeRadialCritical,
    evalPlane_pderiv_swap_zero, evalPlane_pderiv_swap_one]
  simp only [Prod.fst_swap, Prod.snd_swap]
  simp [swapPoint, mkPoint2]

 
theorem planeSquaredRadius_swap (a : PachDeZeeuw.Algebraic.Point2) (z : ℝ × ℝ) :
    planeSquaredRadius (swapPoint a) z.swap = planeSquaredRadius a z := by
  simp [planeSquaredRadius, swapPoint, mkPoint2, add_comm]


theorem exists_localRadialInverse_of_partial0 (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hpartial : evalPlane (pderiv 0 G) z ≠ 0)
    (hradial : evalPlane (planeRadialCritical G a) z ≠ 0) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ (planeSquaredRadius a z) = z ∧ ContinuousAt γ (planeSquaredRadius a z) ∧
      (∀ᶠ r in 𝓝 (planeSquaredRadius a z),
        evalPlane G (γ r) = 0 ∧ planeSquaredRadius a (γ r) = r) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 → γ (planeSquaredRadius a w) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ planeSquaredRadius a z ∈ U ∧ ContinuousOn γ U) := by
  let H : PlanePoly := rename (Equiv.swap 0 1) G
  have hzH : evalPlane H z.swap = 0 := by
    simpa only [H, Prod.swap, evalPlane_rename_swap, Prod.mk.eta] using hz
  have hpH : evalPlane (pderiv 1 H) z.swap ≠ 0 := by
    simpa only [H, evalPlane_pderiv_swap_one] using hpartial
  have hrH : evalPlane (planeRadialCritical H (swapPoint a)) z.swap ≠ 0 := by
    simpa only [H, evalPlane_radialCritical_swap, neg_ne_zero] using hradial
  obtain ⟨γ, hbase, hcont, hright, hleft, hcontOn⟩ :=
    exists_localRadialInverse_of_partial1 H (swapPoint a) hzH hpH hrH
  rw [planeSquaredRadius_swap] at hbase hcont hright hcontOn
  refine ⟨Prod.swap ∘ γ, ?_, continuous_swap.continuousAt.comp hcont, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hbase, Prod.swap_swap]
  · filter_upwards [hright] with r hr
    constructor
    · change evalPlane G ((γ r).2, (γ r).1) = 0
      rw [← evalPlane_rename_swap G (γ r).1 (γ r).2]
      exact hr.1
    · exact (planeSquaredRadius_swap a (γ r).swap).symm.trans hr.2
  · have hl := (continuous_swap.continuousAt :
        ContinuousAt (Prod.swap : ℝ × ℝ → ℝ × ℝ) z).eventually hleft
    filter_upwards [hl] with w hw
    intro hGw
    have hH : evalPlane H w.swap = 0 := by
      simpa only [H, Prod.swap, evalPlane_rename_swap, Prod.mk.eta] using hGw
    have he := hw hH
    dsimp only [Function.comp_apply]
    rw [← planeSquaredRadius_swap a w, he, Prod.swap_swap]
  · obtain ⟨U, hU, hzU, hγU⟩ := hcontOn
    exact ⟨U, hU, hzU, continuous_swap.comp_continuousOn hγU⟩


theorem exists_localRadialInverse (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hradial : evalPlane (planeRadialCritical G a) z ≠ 0) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ (planeSquaredRadius a z) = z ∧ ContinuousAt γ (planeSquaredRadius a z) ∧
      (∀ᶠ r in 𝓝 (planeSquaredRadius a z),
        evalPlane G (γ r) = 0 ∧ planeSquaredRadius a (γ r) = r) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 → γ (planeSquaredRadius a w) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ planeSquaredRadius a z ∈ U ∧ ContinuousOn γ U) := by
  by_cases hp : evalPlane (pderiv 1 G) z ≠ 0
  · exact exists_localRadialInverse_of_partial1 G a hz hp hradial
  · have hp0 : evalPlane (pderiv 0 G) z ≠ 0 := by
      intro hp0
      apply hradial
      rw [evalPlane_planeRadialCritical, hp0, not_ne_iff.mp hp]
      ring
    exact exists_localRadialInverse_of_partial0 G a hz hp0 hradial


theorem planeSquaredRadius_chart (a z : PachDeZeeuw.Algebraic.Point2) :
    planeSquaredRadius a (chartEquiv z) = dist z a ^ 2 := by
  have hm : mkPoint2 (z 0) (z 1) = z := by
    ext i
    fin_cases i <;> simp [mkPoint2]
  simpa only [chartEquiv_apply, hm] using planeSquaredRadius_eq_dist_sq a (z 0, z 1)


theorem exists_planeCurve_localSquaredRadiusInverse (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {z : PachDeZeeuw.Algebraic.Point2}
    (hz : z ∈ PlaneCurveZeroSet G)
    (hradial : MvPolynomial.eval (fun i ↦ z i) (planeRadialCritical G a) ≠ 0) :
    ∃ γ : ℝ → PachDeZeeuw.Algebraic.Point2,
      γ (dist z a ^ 2) = z ∧ ContinuousAt γ (dist z a ^ 2) ∧
      (∀ᶠ r in 𝓝 (dist z a ^ 2), γ r ∈ PlaneCurveZeroSet G ∧ dist (γ r) a ^ 2 = r) ∧
      (∀ᶠ w in 𝓝 z, w ∈ PlaneCurveZeroSet G → γ (dist w a ^ 2) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ dist z a ^ 2 ∈ U ∧ ContinuousOn γ U) := by
  have hz' : evalPlane G (chartEquiv z) = 0 := by
    rw [← eval_eq_evalPlane_chart]
    exact hz
  have hr' : evalPlane (planeRadialCritical G a) (chartEquiv z) ≠ 0 := by
    rwa [← eval_eq_evalPlane_chart]
  obtain ⟨γ, hbase, hcont, hright, hleft, hcontOn⟩ := exists_localRadialInverse G a hz' hr'
  rw [planeSquaredRadius_chart] at hbase hcont hright hcontOn
  refine ⟨chartEquiv.symm ∘ γ, ?_,
    chartEquiv.symm.continuous.continuousAt.comp hcont, ?_, ?_, ?_⟩
  · simp only [Function.comp_apply, hbase, Homeomorph.symm_apply_apply]
  · filter_upwards [hright] with r hr
    constructor
    · change MvPolynomial.eval (fun i ↦ chartEquiv.symm (γ r) i) G = 0
      rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply]
      exact hr.1
    · have hρ := planeSquaredRadius_chart a (chartEquiv.symm (γ r))
      rw [Homeomorph.apply_symm_apply] at hρ
      exact hρ.symm.trans hr.2
  · have hl := chartEquiv.continuous.continuousAt.eventually hleft
    filter_upwards [hl] with w hw
    intro hwG
    have hwG' : evalPlane G (chartEquiv w) = 0 := by
      rw [← eval_eq_evalPlane_chart]
      exact hwG
    have he := congrArg chartEquiv.symm (hw hwG')
    simpa only [planeSquaredRadius_chart, Homeomorph.symm_apply_apply, Function.comp_apply] using he
  · obtain ⟨U, hU, hzU, hγU⟩ := hcontOn
    exact ⟨U, hU, hzU, chartEquiv.symm.continuous.comp_continuousOn hγU⟩


theorem isLocalHomeomorph_planeCurve_squaredRadius (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) :
    IsLocalHomeomorph (fun z : planeCurveRadialRegularLocus G a ↦ dist (z : PachDeZeeuw.Algebraic.Point2) a ^ 2) := by
  classical
  let S := planeCurveRadialRegularLocus G a
  apply isLocalHomeomorph_of_inverse_germs (by fun_prop)
  intro x
  obtain ⟨γ, hbase, hcont, hright, hleft, U, hU, hxU, hγU⟩ :=
    exists_planeCurve_localSquaredRadiusInverse G a x.property.1 x.property.2
  have hRcont : Continuous (fun z : PachDeZeeuw.Algebraic.Point2 ↦
      MvPolynomial.eval (fun i ↦ z i) (planeRadialCritical G a)) :=
    (MvPolynomial.continuous_eval (planeRadialCritical G a)).comp
      (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ))
  have hRg := hRcont.continuousAt.comp hcont
  have hne : ∀ᶠ r in 𝓝 (dist (x : PachDeZeeuw.Algebraic.Point2) a ^ 2),
      MvPolynomial.eval (fun i ↦ γ r i) (planeRadialCritical G a) ≠ 0 :=
    (hRg.ne_iff_eventually_ne continuousAt_const).mp (by
      simp only [Function.comp_apply, hbase]
      exact x.property.2)
  have hgood : ∀ᶠ r in 𝓝 (dist (x : PachDeZeeuw.Algebraic.Point2) a ^ 2), γ r ∈ S := by
    filter_upwards [hright, hne] with r hr hn
    exact ⟨hr.1, hn⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hgood
  let δ : ℝ → S := fun r ↦ if h : γ r ∈ S then ⟨γ r, h⟩ else x
  have hδ : ∀ r, γ r ∈ S → (δ r : PachDeZeeuw.Algebraic.Point2) = γ r := by
    intro r hr
    simp only [δ, dif_pos hr]
  refine ⟨δ, ?_, U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [hδ _ (by rw [hbase]; exact x.property), hbase]
  · apply IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (hγU.mono inter_subset_left).congr (fun r hr ↦ hδ r (hVsub hr.2))
  · filter_upwards [hright, hgood] with r hr hg
    change dist (δ r : PachDeZeeuw.Algebraic.Point2) a ^ 2 = r
    rw [hδ r hg]
    exact hr.2
  · have hl := (continuous_subtype_val.continuousAt :
        ContinuousAt (Subtype.val : S → PachDeZeeuw.Algebraic.Point2) x).eventually hleft
    filter_upwards [hl] with y hy
    have he := hy y.property.1
    apply Subtype.ext
    rw [hδ _ (by rw [he]; exact y.property), he]

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

 
theorem eval_planeGradientSquare (G : PlanePoly) (z : PachDeZeeuw.Algebraic.Point2) :
    MvPolynomial.eval (fun i ↦ z i) (planeGradientSquare G) =
      (MvPolynomial.eval (fun i ↦ z i) (pderiv (0 : Fin 2) G)) ^ 2 +
        (MvPolynomial.eval (fun i ↦ z i) (pderiv (1 : Fin 2) G)) ^ 2 := by
  simp [planeGradientSquare]

 
theorem planeGradientSquare_eval_pos_iff_not_mem_singular
    {G : PlanePoly} {z : PachDeZeeuw.Algebraic.Point2} (hz : z ∈ PlaneCurveZeroSet G) :
    0 < MvPolynomial.eval (fun i ↦ z i) (planeGradientSquare G) ↔
      z ∉ SingularPointSet G := by
  rw [eval_planeGradientSquare]
  constructor
  · intro hpos hsing
    rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff] at hsing
    rcases hsing with ⟨⟨_, hzero₀⟩, hzero₁⟩
    rw [hzero₀, hzero₁] at hpos
    norm_num at hpos
  · intro hregular
    by_cases hzero₀ :
        MvPolynomial.eval (fun i ↦ z i) (pderiv (0 : Fin 2) G) = 0
    · by_cases hzero₁ :
          MvPolynomial.eval (fun i ↦ z i) (pderiv (1 : Fin 2) G) = 0
      · exfalso
        apply hregular
        rw [SingularPointSet, Set.mem_inter_iff, Set.mem_inter_iff]
        exact ⟨⟨hz, hzero₀⟩, hzero₁⟩
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hzero₁)
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hzero₀) (sq_nonneg _)

 
theorem exists_safe_positive_gradient_cutoff_level
    {G : PlanePoly} (hG : Irreducible G) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G) :
    ∃ ε : ℝ, 0 < ε ∧ ¬ G ∣ planeGradientCutoff G ε ∧
      ∀ p ∈ S, p ∉ SingularPointSet G →
        ε < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) := by
  classical
  let R : Finset PachDeZeeuw.Algebraic.Point2 := S.filter (fun p ↦ p ∉ SingularPointSet G)
  by_cases hR : R.Nonempty
  · let V : Finset ℝ := R.image
      (fun p ↦ MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G))
    have hV : V.Nonempty := hR.image _
    let m : ℝ := V.min' hV
    have hm_pos : 0 < m := by
      have hv : m ∈ V := Finset.min'_mem V hV
      rcases Finset.mem_image.mp hv with ⟨p, hp, hpm⟩
      rw [← hpm]
      exact (planeGradientSquare_eval_pos_iff_not_mem_singular
        (hS p (Finset.mem_filter.mp hp).1)).mpr (Finset.mem_filter.mp hp).2
    have hm_le : ∀ p ∈ R,
        m ≤ MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) := by
      intro p hp
      exact Finset.min'_le V _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    let ε₁ : ℝ := m / 2
    let ε₂ : ℝ := m / 3
    have hε₁ : 0 < ε₁ := by dsimp [ε₁]; positivity
    have hε₂ : 0 < ε₂ := by dsimp [ε₂]; positivity
    have hbelow₁ : ∀ p ∈ S, p ∉ SingularPointSet G →
        ε₁ < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) := by
      intro p hp hregular
      have hpR : p ∈ R := Finset.mem_filter.mpr ⟨hp, hregular⟩
      have hmin := hm_le p hpR
      dsimp [ε₁]
      nlinarith
    have hbelow₂ : ∀ p ∈ S, p ∉ SingularPointSet G →
        ε₂ < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) := by
      intro p hp hregular
      have hpR : p ∈ R := Finset.mem_filter.mpr ⟨hp, hregular⟩
      have hmin := hm_le p hpR
      dsimp [ε₂]
      nlinarith
    have hchoice :
        ¬ G ∣ planeGradientCutoff G ε₁ ∨
          ¬ G ∣ planeGradientCutoff G ε₂ := by
      by_cases hbad₁ : G ∣ planeGradientCutoff G ε₁
      · right
        intro hbad₂
        have heq := planeGradientCutoff_forbidden_constant_at_most_one hG hbad₁ hbad₂
        dsimp [ε₁, ε₂] at heq
        nlinarith
      · exact Or.inl hbad₁
    rcases hchoice with hgood₁ | hgood₂
    · exact ⟨ε₁, hε₁, hgood₁, hbelow₁⟩
    · exact ⟨ε₂, hε₂, hgood₂, hbelow₂⟩
  · have hchoice :
        ¬ G ∣ planeGradientCutoff G 1 ∨
          ¬ G ∣ planeGradientCutoff G 2 := by
      by_cases hbad₁ : G ∣ planeGradientCutoff G 1
      · right
        intro hbad₂
        have heq := planeGradientCutoff_forbidden_constant_at_most_one hG hbad₁ hbad₂
        norm_num at heq
      · exact Or.inl hbad₁
    rcases hchoice with hgood₁ | hgood₂
    · refine ⟨1, by norm_num, hgood₁, ?_⟩
      intro p hp hregular
      exfalso
      apply hR
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hregular⟩⟩
    · refine ⟨2, by norm_num, hgood₂, ?_⟩
      intro p hp hregular
      exfalso
      apply hR
      exact ⟨p, Finset.mem_filter.mpr ⟨hp, hregular⟩⟩

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial

private theorem inline_Esgk_TwoPairDistanceNormalization__pairAffineIsometry_map_injective
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    Function.Injective (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) := by
  intro z w hzw
  apply Prod.ext
  · exact g₁.injective (congrArg Prod.fst hzw)
  · exact g₂.injective (congrArg Prod.snd hzw)

theorem pairAffineIsometry_image_twoPairDistanceCommonZeroSet_eq
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂) :
    (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2)) ''
        twoPairDistanceCommonZeroSet C a c b d =
      normalizedDistancePairCommonZeroSet
        (C.affineIsometryTransport g₁)
        (C.affineIsometryTransport g₂) r₁ r₂ := by
  apply Set.Subset.antisymm
  · exact pairAffineIsometry_image_twoPairDistanceCommonZeroSet_subset
      C g₁ g₂ a c b d hg₁a hg₁c hg₂b hg₂d
  · intro w hw
    change w.1 ∈ PlaneCurveZeroSet
        (C.affineIsometryTransport g₁).polynomial ∧
      w.2 ∈ PlaneCurveZeroSet
        (C.affineIsometryTransport g₂).polynomial ∧
      normalizedLeftValue r₁ w.1 = normalizedLeftValue r₂ w.2 ∧
      normalizedRightValue r₁ w.1 = normalizedRightValue r₂ w.2 at hw
    let z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 := (g₁.symm w.1, g₂.symm w.2)
    have hz : z ∈ twoPairDistanceCommonZeroSet C a c b d := by
      change g₁.symm w.1 ∈ PlaneCurveZeroSet C.polynomial ∧
        g₂.symm w.2 ∈ PlaneCurveZeroSet C.polynomial ∧
        dist (g₁.symm w.1) a ^ 2 = dist (g₂.symm w.2) b ^ 2 ∧
        dist (g₁.symm w.1) c ^ 2 = dist (g₂.symm w.2) d ^ 2
      have hzero₁ :=
        (C.mem_zeroSet_affineIsometryTransport_iff g₁ w.1).mp hw.1
      have hzero₂ :=
        (C.mem_zeroSet_affineIsometryTransport_iff g₂ w.2).mp hw.2.1
      have hleft := hw.2.2.1
      rw [normalizedLeftValue_eq_dist_xAxisPoint_neg,
        normalizedLeftValue_eq_dist_xAxisPoint_neg,
        ← hg₁a, ← hg₂b] at hleft
      have hmap₁ := congrArg (fun t : ℝ ↦ t ^ 2)
        (g₁.dist_map (g₁.symm w.1) a)
      have hmap₂ := congrArg (fun t : ℝ ↦ t ^ 2)
        (g₂.dist_map (g₂.symm w.2) b)
      simp only [AffineIsometryEquiv.apply_symm_apply] at hmap₁ hmap₂
      have hleft' : dist (g₁.symm w.1) a ^ 2 =
          dist (g₂.symm w.2) b ^ 2 := by
        simpa using hmap₁.symm.trans (hleft.trans hmap₂)
      have hright := hw.2.2.2
      rw [normalizedRightValue_eq_dist_xAxisPoint,
        normalizedRightValue_eq_dist_xAxisPoint,
        ← hg₁c, ← hg₂d] at hright
      have hmap₃ := congrArg (fun t : ℝ ↦ t ^ 2)
        (g₁.dist_map (g₁.symm w.1) c)
      have hmap₄ := congrArg (fun t : ℝ ↦ t ^ 2)
        (g₂.dist_map (g₂.symm w.2) d)
      simp only [AffineIsometryEquiv.apply_symm_apply] at hmap₃ hmap₄
      have hright' : dist (g₁.symm w.1) c ^ 2 =
          dist (g₂.symm w.2) d ^ 2 := by
        simpa using hmap₃.symm.trans (hright.trans hmap₄)
      exact ⟨hzero₁, hzero₂, hleft', hright'⟩
    refine ⟨z, hz, ?_⟩
    change (g₁ (g₁.symm w.1), g₂ (g₂.symm w.2)) = w
    simp

theorem normalizedDistancePairCommonZeroSet_finite_of_twoPair_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hfinite : (twoPairDistanceCommonZeroSet C a c b d).Finite) :
    (normalizedDistancePairCommonZeroSet
      (C.affineIsometryTransport g₁)
      (C.affineIsometryTransport g₂) r₁ r₂).Finite := by
  rw [← pairAffineIsometry_image_twoPairDistanceCommonZeroSet_eq
    C g₁ g₂ a c b d hg₁a hg₁c hg₂b hg₂d]
  exact hfinite.image (fun z : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 ↦ (g₁ z.1, g₂ z.2))

theorem normalizedDistancePairCommonZeroSet_ncard_eq_twoPairDistanceCommonZeroSet_ncard
    (C : IrreduciblePlanePolynomial ℝ)
    (g₁ g₂ : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) {r₁ r₂ : ℝ}
    (a c b d : PachDeZeeuw.Algebraic.Point2)
    (hg₁a : g₁ a = xAxisPoint (-r₁))
    (hg₁c : g₁ c = xAxisPoint r₁)
    (hg₂b : g₂ b = xAxisPoint (-r₂))
    (hg₂d : g₂ d = xAxisPoint r₂)
    (hfinite : (twoPairDistanceCommonZeroSet C a c b d).Finite) :
    (normalizedDistancePairCommonZeroSet
      (C.affineIsometryTransport g₁)
      (C.affineIsometryTransport g₂) r₁ r₂).ncard =
      (twoPairDistanceCommonZeroSet C a c b d).ncard := by
  rw [← pairAffineIsometry_image_twoPairDistanceCommonZeroSet_eq
    C g₁ g₂ a c b d hg₁a hg₁c hg₂b hg₂d]
  exact Set.ncard_image_of_injective _
    (inline_Esgk_TwoPairDistanceNormalization__pairAffineIsometry_map_injective g₁ g₂)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial


private theorem inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_zero (x y : ℝ) : bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint x y 0 = x := by
  simp [bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint]

private theorem inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_one (x y : ℝ) : bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint x y 1 = y := by
  simp [bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint]

theorem distanceQuadricChart_fst_snd_sum (u v : ℝ) (z : PachDeZeeuw.Algebraic.Point2)
    (hs : z 1 ≠ 0) :
    (distanceQuadricChart u v z).1 1 +
        (distanceQuadricChart u v z).2 1 = z 1 := by
  simp [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK]
  field_simp [hs]
  ring

theorem distanceQuadricChart_injective
    {u v : ℝ} (hv : v ≠ 0) :
    Set.InjOn (distanceQuadricChart u v)
      {z : PachDeZeeuw.Algebraic.Point2 | z 1 ≠ 0} := by
  intro z hz w hw hzw
  have hfirst : v * (z 0) = v * (w 0) := by
    simpa [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint] using
      congrArg (fun p : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 => p.1 0) hzw
  have hz0 : z 0 = w 0 := by
    apply (mul_left_cancel₀ hv)
    exact hfirst
  have hsumz := distanceQuadricChart_fst_snd_sum u v z hz
  have hsumw := distanceQuadricChart_fst_snd_sum u v w hw
  have hz1 : z 1 = w 1 := by
    calc
      z 1 = (distanceQuadricChart u v z).1 1 +
          (distanceQuadricChart u v z).2 1 := hsumz.symm
      _ = (distanceQuadricChart u v w).1 1 +
          (distanceQuadricChart u v w).2 1 := by rw [hzw]
      _ = w 1 := hsumw
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

theorem distanceQuadricChart_normalized_equalities
    {u v : ℝ} {z : PachDeZeeuw.Algebraic.Point2} (hs : z 1 ≠ 0) :
    normalizedLeftValue u (distanceQuadricChart u v z).1 =
        normalizedLeftValue v (distanceQuadricChart u v z).2 ∧
    normalizedRightValue u (distanceQuadricChart u v z).1 =
        normalizedRightValue v (distanceQuadricChart u v z).2 := by
  simp only [normalizedLeftValue, normalizedRightValue, distanceQuadricChart,
    inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_zero, inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_one, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK]
  constructor <;> field_simp [hs] <;> ring

theorem distanceQuadricChart_eq_of_normalized_equalities
    {u v : ℝ} (hv : v ≠ 0) {x y : PachDeZeeuw.Algebraic.Point2} (hs : x 1 + y 1 ≠ 0)
    (hleft : normalizedLeftValue u x = normalizedLeftValue v y)
    (hright : normalizedRightValue u x = normalizedRightValue v y) :
    distanceQuadricChart u v
        (bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (x 0 / v) (x 1 + y 1)) = (x, y) := by
  have hlin : u * (x 0) = v * (y 0) := by
    dsimp [normalizedLeftValue, normalizedRightValue] at hleft hright
    nlinarith
  have hy0 : y 0 = u * (x 0 / v) := by
    field_simp [hv]
    nlinarith [hlin]
  have hformula : x 1 ^ 2 - y 1 ^ 2 =
      (u ^ 2 - v ^ 2) * ((x 0 / v) ^ 2 - 1) := by
    dsimp [normalizedLeftValue, normalizedRightValue] at hleft hright
    rw [hy0] at hleft hright
    field_simp [hv] at hleft hright ⊢
    nlinarith [hleft, hright]
  apply Prod.ext
  · ext i
    fin_cases i
    · simp [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK] <;> field_simp [hv]
    · dsimp [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK]
      rw [← hformula]
      field_simp [hs]
      <;> ring
  · ext i
    fin_cases i
    · simp [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK] <;>
        field_simp [hv] <;> nlinarith [hy0]
    · dsimp [distanceQuadricChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK]
      rw [← hformula]
      field_simp [hs]
      <;> ring

theorem distanceQuadricExceptionalChart_injective
    {u v : ℝ} (hv : v ≠ 0) :
    Function.Injective (distanceQuadricExceptionalChart u v) := by
  intro z w hzw
  have hfirst : v * (z 0) = v * (w 0) := by
    simpa [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint] using
      congrArg (fun p : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 => p.1 0) hzw
  have hz0 : z 0 = w 0 := by
    apply (mul_left_cancel₀ hv)
    exact hfirst
  have hz1 : z 1 = w 1 := by
    have hsecond := congrArg (fun p : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 => p.1 1) hzw
    simpa [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint] using hsecond
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

theorem distanceQuadricExceptionalChart_normalized_iff
    {u v : ℝ} (z : PachDeZeeuw.Algebraic.Point2) :
    normalizedLeftValue u (distanceQuadricExceptionalChart u v z).1 =
        normalizedLeftValue v (distanceQuadricExceptionalChart u v z).2 ∧
    normalizedRightValue u (distanceQuadricExceptionalChart u v z).1 =
        normalizedRightValue v (distanceQuadricExceptionalChart u v z).2 ↔
      bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK u v * (z 0 ^ 2 - 1) = 0 := by
  simp only [normalizedLeftValue, normalizedRightValue,
    distanceQuadricExceptionalChart, inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_zero,
    inline_Esgk_TwoPairDistanceQuadricCharts__quadricPoint_apply_one, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricK]
  constructor
  · intro h
    nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith

theorem distanceQuadricExceptionalChart_eq_of_normalized_equalities
    {u v : ℝ} (hv : v ≠ 0) {x y : PachDeZeeuw.Algebraic.Point2} (hs : x 1 + y 1 = 0)
    (hleft : normalizedLeftValue u x = normalizedLeftValue v y)
    (hright : normalizedRightValue u x = normalizedRightValue v y) :
    distanceQuadricExceptionalChart u v
        (bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint (x 0 / v) (x 1)) = (x, y) := by
  have hlin : u * (x 0) = v * (y 0) := by
    dsimp [normalizedLeftValue, normalizedRightValue] at hleft hright
    nlinarith
  have hy1 : y 1 = -(x 1) := by linarith
  have hy0 : y 0 = u * (x 0 / v) := by
    field_simp [hv]
    nlinarith [hlin]
  apply Prod.ext
  · ext i
    fin_cases i
    · simp [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint] <;> field_simp [hv]
    · simp [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint]
  · ext i
    fin_cases i
    · simp [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint] <;>
        field_simp [hv] <;> nlinarith [hy0]
    · simpa [distanceQuadricExceptionalChart, bundle_Esgk_TwoPairDistanceQuadricCharts_quadricPoint, hy1]

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


theorem isotropicAffineCircularChartI_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartI
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((isotropicAffineCircularChartI.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartI, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]


theorem isotropicAffineCircularChartJ_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    isotropicAffineCircularChartJ
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((isotropicAffineCircularChartJ.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [isotropicAffineCircularChartJ, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_MaximallyCircularIsotropicBidegree__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

 
theorem planeToIsotropicCoordinates_homogeneousComponent
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_MaximallyCircularIsotropicBidegree__planeToIsotropicCoordinates_isHomogeneous
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

 
theorem realToComplexPlanePolynomial_homogeneousComponent
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


theorem projectiveCircularChartI_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      isotropicHomogenizedCircularChartI D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartI]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartI_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

 
theorem projectiveCircularChartJ_planeHomogenization_eq_isotropic
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      isotropicHomogenizedCircularChartJ D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [isotropicHomogenizedCircularChartJ]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← isotropicAffineCircularChartJ_planeToIsotropic_realToComplex]
  congr 1
  rw [realToComplexPlanePolynomial_homogeneousComponent,
    planeToIsotropicCoordinates_homogeneousComponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree

 
theorem isotropicHomogenizedCircularChartI_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartI D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartI]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree

 
theorem isotropicHomogenizedCircularChartJ_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    isotropicHomogenizedCircularChartJ D Q =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  rw [isotropicHomogenizedCircularChartJ]
  exact inline_Esgk_MaximallyCircularIsotropicBidegree__homogenized_eval₂_eq_support_sum D Q _ _ hdegree


@[simp]
theorem isotropicILeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 0 = e 0 := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicILeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicILeadingExponent D e 1 = D - e.degree := by
  simp [isotropicILeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_zero (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 0 = e 1 := by
  simp [isotropicJLeadingExponent]

@[simp]
theorem isotropicJLeadingExponent_one (D : ℕ) (e : Fin 2 →₀ ℕ) :
    isotropicJLeadingExponent D e 1 = D - e.degree := by
  simp [isotropicJLeadingExponent]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicILeadingExponent D e).degree = D - e 1 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicILeadingExponent_zero,
    isotropicILeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree
    (D : ℕ) (e : Fin 2 →₀ ℕ) (he : e.degree ≤ D) :
    (isotropicJLeadingExponent D e).degree = D - e 0 := by
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at he
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add, isotropicJLeadingExponent_zero,
    isotropicJLeadingExponent_one, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e]
  omega

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support
    {P : CircularChartPoly} {m : Fin 2 →₀ ℕ} {i : Fin 2} {n : ℕ}
    (hm : m ∈ P.support) (hdvd : MvPolynomial.X i ^ n ∣ P) : n ≤ m i := by
  rcases hdvd with ⟨R, rfl⟩
  have hcoeff : MvPolynomial.coeff m (MvPolynomial.X i ^ n * R) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_monomial_mul'] at hcoeff
  split at hcoeff
  next hle =>
    have := hle i
    simpa using this
  next hnot => exact (hcoeff rfl).elim

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartITerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hV : MvPolynomial.degreeOf 1
      (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_sub_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hUpow := MvPolynomial.degreeOf_pow_le 1
    (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hVpow := MvPolynomial.degreeOf_pow_le 1
    (2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hUpowZero : MvPolynomial.degreeOf 1
      ((MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hUpow
  have hVpowZero : MvPolynomial.degreeOf 1
      ((2 - MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hV
    simpa [hV] using hVpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hUpowZero ⊢
    simpa [hUpowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero] at hleftZero hVpowZero ⊢
    simpa [hleftZero, hVpowZero] using hmiddle
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartITerm D e c).support) :
    e 0 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 0 ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C (Complex.I ^ e 0) *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartITerm, mul_pow, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartITerm D e c := by
    refine ⟨MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartITerm]
    ring
  have hzero : e 0 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartITerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicCircularChartITerm D e c) =
      c * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicCircularChartITerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 0) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  rw [mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  simp only [← mul_assoc, MvPolynomial.C_mul_monomial]
  rw [MvPolynomial.coeff_monomial_mul']
  simp only [le_refl, if_true, tsub_self]
  rw [← MvPolynomial.constantCoeff_eq, map_pow]
  have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
    change MvPolynomial.constantCoeff
      (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
    simp
  rw [map_sub, map_mul, htwo, MvPolynomial.constantCoeff_C,
    MvPolynomial.constantCoeff_X, mul_zero, sub_zero]
  ring

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 1 ≤ e 1) :
    MvPolynomial.coeff (isotropicILeadingExponent D e)
        (isotropicHomogenizedCircularChartI D Q) =
      MvPolynomial.coeff e Q * Complex.I ^ e 0 * (2 : ℂ) ^ e 1 := by
  classical
  rw [isotropicHomogenizedCircularChartI_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicILeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (2 - MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicILeadingExponent D e)
            (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicILeadingExponent D e ∈
              (isotropicCircularChartITerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coordinate_bounds D f
              (isotropicILeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicILeadingExponent_one] at hone
            omega
          have honeLe : f 1 ≤ e 1 := hmax f hf
          rw [isotropicILeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartITerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartITerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartITerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.degreeOf 1 (isotropicCircularChartJTerm D e c) ≤ D - e.degree := by
  have hU : MvPolynomial.degreeOf 1
      (MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    simpa [circularChartU, MvPolynomial.degreeOf_X, show (1 : Fin 2) ≠ 0 by decide]
      using MvPolynomial.degreeOf_mul_le 1
        (MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
  have hA : MvPolynomial.degreeOf 1
      (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    exact (MvPolynomial.degreeOf_add_le 1 (2 : CircularChartPoly)
      (MvPolynomial.C Complex.I * circularChartU)).trans
        (max_le (by
          change MvPolynomial.degreeOf 1
            (MvPolynomial.C (2 : ℂ) : CircularChartPoly) ≤ 0
          simp) hU)
  have hB : MvPolynomial.degreeOf 1
      (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ≤ 0 := by
    have hmul := MvPolynomial.degreeOf_mul_le 1
      (-MvPolynomial.C Complex.I : CircularChartPoly) circularChartU
    simpa [circularChartU, MvPolynomial.degreeOf_X,
      show (1 : Fin 2) ≠ 0 by decide] using hmul
  have hApow := MvPolynomial.degreeOf_pow_le 1
    (2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 0)
  have hBpow := MvPolynomial.degreeOf_pow_le 1
    (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) (e 1)
  have hleft := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c : CircularChartPoly)
    ((2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
  have hmiddle := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0)
    ((-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
  have hZpow := MvPolynomial.degreeOf_pow_le 1 circularChartZ (D - e.degree)
  have hall := MvPolynomial.degreeOf_mul_le 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1)
    (circularChartZ ^ (D - e.degree))
  have hApowZero : MvPolynomial.degreeOf 1
      ((2 + MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hA
    simpa [hA] using hApow
  have hBpowZero : MvPolynomial.degreeOf 1
      ((-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) ^ e 1) ≤ 0 := by
    rw [Nat.le_zero]
    rw [Nat.le_zero] at hU
    simpa [hU] using hBpow
  have hleftZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0) ≤ 0 := by
    rw [Nat.le_zero] at hApowZero ⊢
    simpa [hApowZero] using hleft
  have hmiddleZero : MvPolynomial.degreeOf 1
      (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
        (-MvPolynomial.C Complex.I * circularChartU) ^ e 1) ≤ 0 := by
    simpa using hmiddle.trans (Nat.add_le_add hleftZero hBpowZero)
  have hZpowBound : MvPolynomial.degreeOf 1
      (circularChartZ ^ (D - e.degree)) ≤ D - e.degree := by
    simpa [circularChartZ] using hZpow
  change MvPolynomial.degreeOf 1
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) ≤ D - e.degree
  simpa using hall.trans (Nat.add_le_add hmiddleZero hZpowBound)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds
    (D : ℕ) (e m : Fin 2 →₀ ℕ) (c : ℂ)
    (hm : m ∈ (isotropicCircularChartJTerm D e c).support) :
    e 1 ≤ m 0 ∧ m 1 = D - e.degree := by
  have hUdvd : circularChartU ^ e 1 ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
      (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      circularChartZ ^ (D - e.degree), ?_⟩
    rw [isotropicCircularChartJTerm, mul_pow, ← map_neg, ← map_pow]
    ring
  have hZdvd : circularChartZ ^ (D - e.degree) ∣ isotropicCircularChartJTerm D e c := by
    refine ⟨MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1, ?_⟩
    rw [isotropicCircularChartJTerm]
    ring
  have hzero : e 1 ≤ m 0 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartU] using hUdvd
  have honeLower : D - e.degree ≤ m 1 := by
    apply inline_Esgk_MaximallyCircularIsotropicBidegree__coordinate_pow_exponent_le_of_dvd_of_mem_support hm
    simpa [circularChartZ] using hZdvd
  have honeUpper : m 1 ≤ D - e.degree :=
    (MvPolynomial.le_degreeOf_of_mem_support 1 hm).trans
      (inline_Esgk_MaximallyCircularIsotropicBidegree__circularChartJTerm_degreeOf_one_le D e c)
  exact ⟨hzero, Nat.le_antisymm honeUpper honeLower⟩

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicCircularChartJTerm D e c) =
      c * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicCircularChartJTerm]
  change MvPolynomial.coeff
    (Finsupp.single 0 (e 1) + Finsupp.single 1 (D - e.degree))
    (MvPolynomial.C c * (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
      (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
      circularChartZ ^ (D - e.degree)) = _
  rw [circularChartZ, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.coeff_mul_monomial, mul_one]
  have hneg : (-MvPolynomial.C Complex.I * circularChartU : CircularChartPoly) =
      MvPolynomial.C (-Complex.I) * circularChartU := by
    rw [map_neg]
  rw [hneg, mul_pow, ← map_pow, circularChartU, MvPolynomial.X_pow_eq_monomial]
  have hreorder :
      (MvPolynomial.C c : CircularChartPoly) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 *
          (MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) =
        MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by
    calc
      _ = (MvPolynomial.C c * MvPolynomial.C ((-Complex.I) ^ e 1) *
            MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1)) 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X (0 : Fin 2)) ^ e 0 := by ring
      _ = _ := by
        rw [← map_mul, MvPolynomial.C_mul_monomial]
        congr 2
        ring
  calc
    _ = MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))
        (MvPolynomial.monomial (Finsupp.single (0 : Fin 2) (e 1))
            (c * (-Complex.I) ^ e 1) *
          (2 + MvPolynomial.C Complex.I * MvPolynomial.X 0) ^ e 0) :=
      congrArg (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) (e 1))) hreorder
    _ = _ := by
      rw [MvPolynomial.coeff_monomial_mul']
      simp only [le_refl, if_true, tsub_self]
      rw [← MvPolynomial.constantCoeff_eq, map_pow]
      have htwo : MvPolynomial.constantCoeff (2 : CircularChartPoly) = (2 : ℂ) := by
        change MvPolynomial.constantCoeff
          (MvPolynomial.C (2 : ℂ) : CircularChartPoly) = (2 : ℂ)
        simp
      rw [map_add, map_mul, htwo, MvPolynomial.constantCoeff_C,
        MvPolynomial.constantCoeff_X, mul_zero, add_zero]

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
    (D : ℕ) (Q : ComplexPlanePoly) (e : Fin 2 →₀ ℕ)
    (hdegree : Q.totalDegree ≤ D) (he : e ∈ Q.support)
    (hmax : ∀ f ∈ Q.support, f 0 ≤ e 0) :
    MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (isotropicHomogenizedCircularChartJ D Q) =
      MvPolynomial.coeff e Q * (-Complex.I) ^ e 1 * (2 : ℂ) ^ e 0 := by
  classical
  rw [isotropicHomogenizedCircularChartJ_eq_support_sum D Q hdegree]
  rw [MvPolynomial.coeff_sum]
  calc
    _ = MvPolynomial.coeff (isotropicJLeadingExponent D e)
        (MvPolynomial.C (MvPolynomial.coeff e Q) *
          (2 + MvPolynomial.C Complex.I * circularChartU) ^ e 0 *
          (-MvPolynomial.C Complex.I * circularChartU) ^ e 1 *
          circularChartZ ^ (D - e.degree)) := by
      apply Finset.sum_eq_single e
      · intro f hf hfe
        have hfzero : MvPolynomial.coeff (isotropicJLeadingExponent D e)
            (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)) = 0 := by
          by_contra hcoeff
          have hmem : isotropicJLeadingExponent D e ∈
              (isotropicCircularChartJTerm D f (MvPolynomial.coeff f Q)).support :=
            MvPolynomial.mem_support_iff.mpr hcoeff
          obtain ⟨hzero, hone⟩ :=
            inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coordinate_bounds D f
              (isotropicJLeadingExponent D e) (MvPolynomial.coeff f Q) hmem
          have hfdegree : f.degree ≤ D :=
            (MvPolynomial.le_totalDegree hf).trans hdegree
          have hedegree : e.degree ≤ D :=
            (MvPolynomial.le_totalDegree he).trans hdegree
          have hdegreeEq : f.degree = e.degree := by
            rw [isotropicJLeadingExponent_one] at hone
            omega
          have hzeroLe : f 0 ≤ e 0 := hmax f hf
          rw [isotropicJLeadingExponent_zero] at hzero
          have hzeroEq : f 0 = e 0 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          have honeEq : f 1 = e 1 := by
            rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add f, inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add e] at hdegreeEq
            omega
          apply hfe
          apply Finsupp.ext
          intro i
          fin_cases i
          · exact hzeroEq
          · exact honeEq
        simpa [isotropicCircularChartJTerm] using hfzero
      · intro hnot
        exact (hnot he).elim
    _ = _ := by
      simpa [isotropicCircularChartJTerm] using
        inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicCircularChartJTerm_coeff_leading D e (MvPolynomial.coeff e Q)

private theorem inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (c : ℂ) {G : PlanePoly} {d : Fin 2 →₀ ℕ}
    (hcoeff : MvPolynomial.coeff d
        (projectiveCircularChart c (planeHomogenization G.totalDegree G)) ≠ 0) :
    planeCircularLocalOrder c G ≤ d.degree := by
  have hcoeffSeries : MvPowerSeries.coeff d
      ((projectiveCircularChart c (planeHomogenization G.totalDegree G) :
        CircularChartPoly) : MvPowerSeries (Fin 2) ℂ) ≠ 0 := by
    simpa using hcoeff
  have horder := MvPowerSeries.order_le hcoeffSeries
  have horderNat := ENat.toNat_le_toNat horder
  simpa [planeCircularLocalOrder, MvPolynomial.localOrder] using horderNat


theorem IsMaximallyCircular.bidegreeBound_planeIsotropicCoordinateEquiv
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (p : ℕ) (hdegree : G.totalDegree = 2 * p) :
    BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  classical
  let Q : ComplexPlanePoly :=
    planeToIsotropicCoordinates (realToComplexPlanePolynomial G)
  have hmapzero : realToComplexPlanePolynomial G ≠ 0 := by
    exact (MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective).ne hG
  have hQzero : Q ≠ 0 := by
    change planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G) ≠ 0
    exact planeIsotropicCoordinateEquiv.injective.ne hmapzero
  have hQdegree : Q.totalDegree ≤ G.totalDegree := by
    change (planeToIsotropicCoordinates
      (realToComplexPlanePolynomial G)).totalDegree ≤ G.totalDegree
    rw [planeToIsotropicCoordinates_totalDegree]
    change (MvPolynomial.map Complex.ofRealHom G).totalDegree ≤ G.totalDegree
    unfold MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective G Complex.ofReal_injective]
  have hsupp : Q.support.Nonempty := MvPolynomial.support_nonempty.mpr hQzero
  obtain ⟨eI, heI, heIsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 1)
  have heImax : ∀ f ∈ Q.support, f 1 ≤ eI 1 := by
    intro f hf
    calc
      f 1 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 1) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 1) hf
      _ = eI 1 := heIsup
  obtain ⟨eJ, heJ, heJsup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupp (fun e : Fin 2 →₀ ℕ ↦ e 0)
  have heJmax : ∀ f ∈ Q.support, f 0 ≤ eJ 0 := by
    intro f hf
    calc
      f 0 ≤ Q.support.sup (fun e : Fin 2 →₀ ℕ ↦ e 0) :=
        Finset.le_sup (f := fun e : Fin 2 →₀ ℕ ↦ e 0) hf
      _ = eJ 0 := heJsup
  have heIdegree : eI.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heI).trans hQdegree
  have heJdegree : eJ.degree ≤ G.totalDegree :=
    (MvPolynomial.le_totalDegree heJ).trans hQdegree
  have hcoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (isotropicHomogenizedCircularChartI G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartI_coeff_extremal
      G.totalDegree Q eI hQdegree heI heImax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heI)
        (pow_ne_zero _ Complex.I_ne_zero))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffI : MvPolynomial.coeff
      (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChart Complex.I
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicILeadingExponent G.totalDegree eI)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartI_planeHomogenization_eq_isotropic]
    exact hcoeffI
  have hlocalI := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    Complex.I hchartCoeffI
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicILeadingExponent_degree G.totalDegree eI heIdegree] at hlocalI
  have horderI : planeCircularLocalOrderI G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heIbound : eI 1 ≤ p := by
    have heIcoord : eI 1 ≤ eI.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderI G ≤ G.totalDegree - eI 1 at hlocalI
    rw [horderI, hdegree] at hlocalI
    omega
  have hcoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (isotropicHomogenizedCircularChartJ G.totalDegree Q) ≠ 0 := by
    rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicHomogenizedCircularChartJ_coeff_extremal
      G.totalDegree Q eJ hQdegree heJ heJmax]
    exact mul_ne_zero
      (mul_ne_zero (MvPolynomial.mem_support_iff.mp heJ)
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)))
      (pow_ne_zero _ (by norm_num))
  have hchartCoeffJ : MvPolynomial.coeff
      (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChart (-Complex.I)
        (planeHomogenization G.totalDegree G)) ≠ 0 := by
    change MvPolynomial.coeff (isotropicJLeadingExponent G.totalDegree eJ)
      (projectiveCircularChartJ (planeHomogenization G.totalDegree G)) ≠ 0
    rw [projectiveCircularChartJ_planeHomogenization_eq_isotropic]
    exact hcoeffJ
  have hlocalJ := inline_Esgk_MaximallyCircularIsotropicBidegree__planeCircularLocalOrder_le_degree_of_coeff_ne_zero
    (-Complex.I) hchartCoeffJ
  rw [inline_Esgk_MaximallyCircularIsotropicBidegree__isotropicJLeadingExponent_degree G.totalDegree eJ heJdegree] at hlocalJ
  have horderJ : planeCircularLocalOrderJ G = p := by
    rcases hmax with ⟨hI, hJ⟩
    omega
  have heJbound : eJ 0 ≤ p := by
    have heJcoord : eJ 0 ≤ eJ.degree := by
      rw [inline_Esgk_MaximallyCircularIsotropicBidegree__finTwo_degree_eq_add]
      omega
    change planeCircularLocalOrderJ G ≤ G.totalDegree - eJ 0 at hlocalJ
    rw [horderJ, hdegree] at hlocalJ
    omega
  change BidegreeBound p Q
  intro e he
  exact ⟨(heJmax e he).trans heJbound, (heImax e he).trans heIbound⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

private theorem complex_I_ne_neg_I' : Complex.I ≠ -Complex.I := by
  intro h
  have him : (1 : ℝ) = -1 := congrArg Complex.im h
  have hlt : (-1 : ℝ) < 1 := lt_trans neg_one_lt_zero zero_lt_one
  exact (ne_of_gt hlt) him


theorem IsMaximallyCircular.rootMultiplicity_I_eq_localOrderI
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I =
      planeCircularLocalOrderI G := by
  have hI : planeCircularLocalOrderI G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I := by
    simpa [planeCircularLocalOrderI] using
      (planeCircularLocalOrder_le_rootMultiplicity Complex.I hG)
  have hJ : planeCircularLocalOrderJ G ≤
      (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) := by
    simpa [planeCircularLocalOrderJ] using
      (planeCircularLocalOrder_le_rootMultiplicity (-Complex.I) hG)
  have hroots :
      (complexPlaneInfinityRestriction G).rootMultiplicity Complex.I +
          (complexPlaneInfinityRestriction G).rootMultiplicity (-Complex.I) ≤ G.totalDegree :=
    (Polynomial.rootMultiplicity_add_rootMultiplicity_le_natDegree_of_ne
      (complexPlaneInfinityRestriction G) complex_I_ne_neg_I').trans
        (complexPlaneInfinityRestriction_natDegree_le G)
  have horders := hmax.order_sum_eq_totalDegree
  omega


theorem chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    (c : ℂ) {G : PlanePoly} (hG : G ≠ 0)
    (hsat : (complexPlaneInfinityRestriction G).rootMultiplicity c =
      planeCircularLocalOrder c G) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrder c G)
          (projectiveCircularChart c (planeHomogenization G.totalDegree G))) ≠ 0 := by
  let m := planeCircularLocalOrder c G
  let F := projectiveCircularChart c (planeHomogenization G.totalDegree G)
  let q := (complexPlaneInfinityRestriction G).comp (Polynomial.X + Polynomial.C c)
  have hq : q ≠ 0 := by
    exact Polynomial.comp_X_add_C_ne_zero_iff.mpr
      (complexPlaneInfinityRestriction_ne_zero hG)
  have hqcoeff : q.coeff q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq
  have hdegree : q.natTrailingDegree = m := by
    calc
      q.natTrailingDegree =
          (complexPlaneInfinityRestriction G).rootMultiplicity c := by
        simpa [q] using
          (Polynomial.rootMultiplicity_eq_natTrailingDegree
            (p := complexPlaneInfinityRestriction G) (t := c)).symm
      _ = m := by simpa [m] using hsat
  have hrestrict : chartInfinityRestriction F = q := by
    exact chartInfinityRestriction_projectiveCircularChart_planeHomogenization c G
  have hcoeffF :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F ≠ 0 := by
    rw [← chartInfinityRestriction_coeff, hrestrict, ← hdegree]
    exact hqcoeff
  have hindexDegree :
      Finsupp.degree (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) = m := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change m + (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) (0 : Fin 1).succ = m
    rw [Finsupp.cons_succ]
    simp
  intro hzero
  apply hcoeffF
  have hcomponentCoeff :
      MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ))
          (MvPolynomial.homogeneousComponent m F) =
        MvPolynomial.coeff (Finsupp.cons m (0 : Fin 1 →₀ ℕ)) F := by
    simp [MvPolynomial.coeff_homogeneousComponent, hindexDegree]
  rw [← hcomponentCoeff, ← chartInfinityRestriction_coeff, hzero]
  simp


theorem IsMaximallyCircular.chartInfinityRestriction_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    chartInfinityRestriction
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact chartInfinityRestriction_homogeneousComponent_ne_zero_of_rootMultiplicity_eq
    Complex.I hG (by
      simpa [planeCircularLocalOrderI] using hmax.rootMultiplicity_I_eq_localOrderI hG)


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem normalizedFactors_toFinset_totalDegree_sum_le (F : PlanePoly) (hF : F ≠ 0) :
    ∑ G ∈ (UniqueFactorizationMonoid.normalizedFactors F).toFinset, G.totalDegree ≤
      F.totalDegree := by
  classical
  let s : Multiset PlanePoly := UniqueFactorizationMonoid.normalizedFactors F
  have hsnonzero : ∀ G ∈ s, G ≠ 0 := by
    intro G hG
    exact (normalized_factor_irreducible (p := F) (h := G) (by simpa [s] using hG)).ne_zero
  have hdegreeProd :
      s.prod.totalDegree = (s.map fun G : PlanePoly ↦ G.totalDegree).sum :=
    helper_multiset_prod_totalDegree_eq_sum s hsnonzero
  have hassoc : Associated s.prod F := by
    simpa [s] using UniqueFactorizationMonoid.prod_normalizedFactors hF
  have hdegreeSum :
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = F.totalDegree := by
    calc
      (s.map fun G : PlanePoly ↦ G.totalDegree).sum = s.prod.totalDegree :=
        hdegreeProd.symm
      _ = F.totalDegree := totalDegree_eq_of_associated hassoc
  have hdedupDegree :
      (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum ≤
        (s.map fun G : PlanePoly ↦ G.totalDegree).sum := by
    rcases Multiset.le_iff_exists_add.mp (Multiset.dedup_le s) with ⟨t, ht⟩
    calc
      (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum ≤
          (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum +
            (t.map fun G : PlanePoly ↦ G.totalDegree).sum := by omega
      _ = ((s.dedup + t).map fun G : PlanePoly ↦ G.totalDegree).sum := by simp
      _ = (s.map fun G : PlanePoly ↦ G.totalDegree).sum := by rw [← ht]
  calc
    ∑ G ∈ (UniqueFactorizationMonoid.normalizedFactors F).toFinset, G.totalDegree =
        (s.dedup.map fun G : PlanePoly ↦ G.totalDegree).sum := by
      change
        (((UniqueFactorizationMonoid.normalizedFactors F).toFinset).1.map
            fun G : PlanePoly ↦ G.totalDegree).sum = _
      rw [Multiset.toFinset_val]
    _ ≤ (s.map fun G : PlanePoly ↦ G.totalDegree).sum := hdedupDegree
    _ = F.totalDegree := hdegreeSum


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Filter Topology MvPolynomial
open PachDeZeeuw.Algebraic

namespace Esgk


private theorem inline_Esgk_PlaneCurveRegularChart__exists_openPartialHomeomorph_of_inverse_germ
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Continuous f) (x : X)
    (γ : Y → X) (hγx : γ (f x) = x)
    (U : Set Y) (hU : IsOpen U) (hfxU : f x ∈ U) (hγU : ContinuousOn γ U)
    (hright : ∀ᶠ y in 𝓝 (f x), f (γ y) = y)
    (hleft : ∀ᶠ z in 𝓝 x, γ (f z) = z) :
    ∃ e : OpenPartialHomeomorph X Y, x ∈ e.source ∧ (∀ z, e z = f z) := by
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hleft
  obtain ⟨R, hRsub, hR, hfxR⟩ := mem_nhds_iff.mp hright
  have hγ_at : ContinuousAt γ (f x) := hγU.continuousAt (hU.mem_nhds hfxU)
  have hW_nhds : W ∈ 𝓝 (γ (f x)) := by
    rw [hγx]
    exact hW.mem_nhds hxW
  obtain ⟨V₀, hV₀sub, hV₀, hfxV₀⟩ :=
    mem_nhds_iff.mp (hγ_at.preimage_mem_nhds hW_nhds)
  let V : Set Y := U ∩ (R ∩ V₀)
  let S : Set X := W ∩ f ⁻¹' V
  have hV : IsOpen V := hU.inter (hR.inter hV₀)
  have hS : IsOpen S := hW.inter (hV.preimage hf)
  let e : OpenPartialHomeomorph X Y :=
    { toFun := f
      invFun := γ
      source := S
      target := V
      map_source' := fun _ hz ↦ hz.2
      map_target' := by
        intro y hy
        refine ⟨hV₀sub hy.2.2, ?_⟩
        change f (γ y) ∈ V
        rw [hRsub hy.2.1]
        exact hy
      left_inv' := fun _ hz ↦ hWsub hz.1
      right_inv' := fun _ hy ↦ hRsub hy.2.1
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hγU.mono inter_subset_left
      open_source := hS
      open_target := hV }
  exact ⟨e, ⟨hxW, hfxU, hfxR, hfxV₀⟩, fun _ ↦ rfl⟩

private theorem inline_Esgk_PlaneCurveRegularChart__exists_coordinateInverse_of_partial1 (G : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane G z = 0) (hp : evalPlane (pderiv 1 G) z ≠ 0) :
    ∃ γ : ℝ → ℝ × ℝ,
      γ z.1 = z ∧ ContinuousAt γ z.1 ∧
      (∀ᶠ r in 𝓝 z.1, evalPlane G (γ r) = 0 ∧ (γ r).1 = r) ∧
      (∀ᶠ w in 𝓝 z, evalPlane G w = 0 → γ w.1 = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ z.1 ∈ U ∧ ContinuousOn γ U) := by
  obtain ⟨ψ, hbase, hψ, hcurve, hlocal⟩ :=
    exists_smooth_implicitGraph_of_partial1 G hz hp
  refine ⟨fun t ↦ (t, ψ t), ?_, continuousAt_id.prodMk hψ.continuousAt, ?_, ?_, ?_⟩
  · simp [hbase]
  · filter_upwards [hcurve] with t ht
    exact ⟨ht, rfl⟩
  · filter_upwards [hlocal] with w hw
    intro hGw
    simp only [hw.mp hGw, Prod.mk.eta]
  · obtain ⟨V, hV, hVψ⟩ : ∃ V ∈ 𝓝 z.1, ContDiffOn ℝ 0 ψ V :=
      hψ.contDiffOn le_top (by simp)
    exact ⟨interior V, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV,
      continuousOn_id.prodMk ((contDiffOn_zero.mp hVψ).mono interior_subset)⟩


theorem exists_planeCurve_localCoordinateInverse (G : PlanePoly)
    {z : PachDeZeeuw.Algebraic.Point2} (hz : z ∈ planeCurveRegularLocus G) :
    ∃ (i : Fin 2) (γ : ℝ → PachDeZeeuw.Algebraic.Point2),
      γ (z i) = z ∧ ContinuousAt γ (z i) ∧
      (∀ᶠ r in 𝓝 (z i), γ r ∈ PlaneCurveZeroSet G ∧ γ r i = r) ∧
      (∀ᶠ w in 𝓝 z, w ∈ PlaneCurveZeroSet G → γ (w i) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ z i ∈ U ∧ ContinuousOn γ U) := by
  have hG : evalPlane G (chartEquiv z) = 0 := by
    rw [← eval_eq_evalPlane_chart]
    exact hz.1
  have hprod : ∃ (i : Fin 2) (γ : ℝ → ℝ × ℝ),
      γ (z i) = chartEquiv z ∧ ContinuousAt γ (z i) ∧
      (∀ᶠ r in 𝓝 (z i), evalPlane G (γ r) = 0 ∧ chartEquiv.symm (γ r) i = r) ∧
      (∀ᶠ w in 𝓝 (chartEquiv z), evalPlane G w = 0 → γ (chartEquiv.symm w i) = w) ∧
      (∃ U : Set ℝ, IsOpen U ∧ z i ∈ U ∧ ContinuousOn γ U) := by
    by_cases hp : evalPlane (pderiv 1 G) (chartEquiv z) ≠ 0
    · obtain ⟨γ, hb, hc, hr, hl, hU⟩ := inline_Esgk_PlaneCurveRegularChart__exists_coordinateInverse_of_partial1 G hG hp
      exact ⟨0, γ, hb, hc, hr, hl, hU⟩
    · have hp0 : evalPlane (pderiv 0 G) (chartEquiv z) ≠ 0 := by
        intro hzero
        apply hz.2
        refine ⟨⟨hz.1, ?_⟩, ?_⟩
        · change MvPolynomial.eval (fun j ↦ z j) (pderiv 0 G) = 0
          rwa [eval_eq_evalPlane_chart]
        · change MvPolynomial.eval (fun j ↦ z j) (pderiv 1 G) = 0
          rw [eval_eq_evalPlane_chart]
          exact not_ne_iff.mp hp
      let H := rename (Equiv.swap (0 : Fin 2) 1) G
      have hH : evalPlane H (chartEquiv z).swap = 0 := by
        simpa only [H, Prod.swap, evalPlane_rename_swap, Prod.mk.eta] using hG
      have hH1 : evalPlane (pderiv 1 H) (chartEquiv z).swap ≠ 0 := by
        simpa only [H, evalPlane_pderiv_swap_one] using hp0
      obtain ⟨γ, hb, hc, hr, hl, U, hU, hzU, hcU⟩ :=
        inline_Esgk_PlaneCurveRegularChart__exists_coordinateInverse_of_partial1 H hH hH1
      refine ⟨1, Prod.swap ∘ γ, ?_, continuous_swap.continuousAt.comp hc, ?_, ?_,
        U, hU, hzU, continuous_swap.comp_continuousOn hcU⟩
      · change (γ (chartEquiv z).swap.1).swap = chartEquiv z
        rw [hb, Prod.swap_swap]
      · filter_upwards [hr] with r hr
        constructor
        · change evalPlane G ((γ r).2, (γ r).1) = 0
          rw [← evalPlane_rename_swap G (γ r).1 (γ r).2]
          exact hr.1
        · exact hr.2
      · have hl' := (continuous_swap.continuousAt :
            ContinuousAt (Prod.swap : ℝ × ℝ → ℝ × ℝ) (chartEquiv z)).eventually hl
        filter_upwards [hl'] with w hw
        intro hwG
        have hHw : evalPlane H w.swap = 0 := by
          simpa only [H, Prod.swap, evalPlane_rename_swap, Prod.mk.eta] using hwG
        simpa only [Function.comp_apply, chartEquiv_symm_apply_one, Prod.fst_swap,
          Prod.swap_swap] using congrArg Prod.swap (hw hHw)
  obtain ⟨i, γ, hb, hc, hr, hl, U, hU, hzU, hcU⟩ := hprod
  refine ⟨i, chartEquiv.symm ∘ γ, ?_, chartEquiv.symm.continuous.continuousAt.comp hc,
    ?_, ?_, U, hU, hzU, chartEquiv.symm.continuous.comp_continuousOn hcU⟩
  · simp only [Function.comp_apply, hb, Homeomorph.symm_apply_apply]
  · filter_upwards [hr] with r hr
    refine ⟨?_, hr.2⟩
    change MvPolynomial.eval (fun i ↦ chartEquiv.symm (γ r) i) G = 0
    rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply]
    exact hr.1
  · have hl' := chartEquiv.continuous.continuousAt.eventually hl
    filter_upwards [hl'] with w hw
    intro hwG
    have hwG' : evalPlane G (chartEquiv w) = 0 := by
      rw [← eval_eq_evalPlane_chart]
      exact hwG
    simpa only [Function.comp_apply, Homeomorph.symm_apply_apply] using
      congrArg chartEquiv.symm (hw hwG')


theorem exists_planeCurveRegular_chart (G : PlanePoly) (x : planeCurveRegularLocus G) :
    ∃ (i : Fin 2) (e : OpenPartialHomeomorph (planeCurveRegularLocus G) ℝ),
      x ∈ e.source ∧ (∀ y, e y = (y : PachDeZeeuw.Algebraic.Point2) i) := by
  classical
  let S := planeCurveRegularLocus G
  obtain ⟨i, γ, hb, hc, hr, hl, U, hU, hxU, hcU⟩ :=
    exists_planeCurve_localCoordinateInverse G x.property
  have hclosed : IsClosed (SingularPointSet G) := by
    change IsClosed ((PlaneCurveZeroSet G ∩
      {z : PachDeZeeuw.Algebraic.Point2 | MvPolynomial.eval (fun j ↦ z j) (pderiv 0 G) = 0}) ∩
      {z : PachDeZeeuw.Algebraic.Point2 | MvPolynomial.eval (fun j ↦ z j) (pderiv 1 G) = 0})
    have hcont : ∀ P : PlanePoly, Continuous (fun z : PachDeZeeuw.Algebraic.Point2 ↦ MvPolynomial.eval (fun j ↦ z j) P) :=
      fun P ↦ (MvPolynomial.continuous_eval P).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ))
    exact ((isClosed_eq (hcont G) continuous_const).inter
      (isClosed_eq (hcont (pderiv 0 G)) continuous_const)).inter
      (isClosed_eq (hcont (pderiv 1 G)) continuous_const)
  have hopen : IsOpen (SingularPointSet G)ᶜ := hclosed.isOpen_compl
  have hn : ∀ᶠ r in 𝓝 ((x : PachDeZeeuw.Algebraic.Point2) i), γ r ∉ SingularPointSet G :=
    hc.preimage_mem_nhds (hopen.mem_nhds (by rw [hb]; exact x.property.2))
  have hgood : ∀ᶠ r in 𝓝 ((x : PachDeZeeuw.Algebraic.Point2) i), γ r ∈ S := by
    filter_upwards [hr, hn] with r hr hn
    exact ⟨hr.1, hn⟩
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hgood
  let δ : ℝ → S := fun r ↦ if h : γ r ∈ S then ⟨γ r, h⟩ else x
  have hδ : ∀ r, γ r ∈ S → (δ r : PachDeZeeuw.Algebraic.Point2) = γ r := by
    intro r h
    simp only [δ, dif_pos h]
  have hbase : δ ((x : PachDeZeeuw.Algebraic.Point2) i) = x := by
    apply Subtype.ext
    rw [hδ _ (by rw [hb]; exact x.property), hb]
  have hcont : ContinuousOn δ (U ∩ V) := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    exact (hcU.mono inter_subset_left).congr (fun r hr ↦ hδ r (hVsub hr.2))
  have hright : ∀ᶠ r in 𝓝 ((x : PachDeZeeuw.Algebraic.Point2) i), (δ r : PachDeZeeuw.Algebraic.Point2) i = r := by
    filter_upwards [hr, hgood] with r hr hg
    rw [hδ r hg]
    exact hr.2
  have hleft : ∀ᶠ y : S in 𝓝 x, δ ((y : PachDeZeeuw.Algebraic.Point2) i) = y := by
    have hl' := (continuous_subtype_val.continuousAt :
      ContinuousAt (Subtype.val : S → PachDeZeeuw.Algebraic.Point2) x).eventually hl
    filter_upwards [hl'] with y hy
    have he := hy y.property.1
    apply Subtype.ext
    rw [hδ _ (by rw [he]; exact y.property), he]
  obtain ⟨e, he, hef⟩ := inline_Esgk_PlaneCurveRegularChart__exists_openPartialHomeomorph_of_inverse_germ
    (f := fun y : S ↦ (y : PachDeZeeuw.Algebraic.Point2) i) (by fun_prop) x δ hbase
    (U ∩ V) (hU.inter hV) ⟨hxU, hxV⟩ hcont hright hleft
  exact ⟨i, e, he, hef⟩

end Esgk
end

end











section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open MvPolynomial


private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le (a : ℝ) (p : PlanePoly) {n : ℕ}
    (hp : p.totalDegree ≤ n) : (C a * p).totalDegree ≤ n := by
  exact (totalDegree_mul _ _).trans (by simpa using hp)

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_X_sq_le (i : Fin 2) : (X i ^ 2 : PlanePoly).totalDegree ≤ 2 := by
  simpa using totalDegree_pow (X i : PlanePoly) 2

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__chartConstraint_degree (k : ℝ) :
    (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint k).totalDegree ≤ 2 := by
  apply inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le
  exact (totalDegree_sub _ _).trans (max_le (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_X_sq_le 0) (by simp))

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__mainChartPullback_degree (d : ℕ) (p : PlanePoly) (a k : ℝ)
    (hp : p.totalDegree ≤ d) : (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback d p a k).totalDegree ≤ 2 * d := by
  apply planePolynomialRationalPullback_totalDegree_le d 2 _ _ _ _ hp
  · change (C (2 * a) * X 0 * X 1 : PlanePoly).totalDegree ≤ 2
    calc
      _ ≤ (C (2 * a) * X 0 : PlanePoly).totalDegree +
          (X (1 : Fin 2) : PlanePoly).totalDegree := totalDegree_mul _ _
      _ ≤ 1 + 1 := Nat.add_le_add (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le _ _ (by simp)) (by simp)
  · exact (totalDegree_add _ _).trans
      (max_le (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_X_sq_le 1) (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__chartConstraint_degree k))
  · exact inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le _ _ (by simp)

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__exceptionalChartPullback_degree (d : ℕ) (p : PlanePoly) (a b : ℝ)
    (hp : p.totalDegree ≤ d) :
    (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback d p a b).totalDegree ≤ d := by
  simpa only [bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback, one_mul] using
    planePolynomialRationalPullback_totalDegree_le d 1 p (C a * X 0) (C b * X 1) 1
      hp (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le _ _ (by simp)) (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__degree_C_mul_le _ _ (by simp)) (by simp)

theorem distanceQuadricMainPolynomial_totalDegree_le
    (d : ℕ) (p q : PlanePoly) (u v : ℝ)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (distanceQuadricMainPolynomial d p q u v).totalDegree ≤ 4 * d := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (by
      have h := inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__mainChartPullback_degree d p v (u ^ 2 - v ^ 2) hp
      omega)
  · exact (totalDegree_pow _ _).trans (by
      have h := inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__mainChartPullback_degree d q u (-(u ^ 2 - v ^ 2)) hq
      omega)

theorem distanceQuadricExceptionalPolynomial_totalDegree_le
    (d : ℕ) (p q : PlanePoly) (u v : ℝ) (hd : 2 ≤ d)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (distanceQuadricExceptionalPolynomial d p q u v).totalDegree ≤ 2 * d := by
  apply (totalDegree_add _ _).trans
  apply max_le
  · exact (totalDegree_pow _ _).trans (by
      have h := inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__chartConstraint_degree (u ^ 2 - v ^ 2)
      omega)
  · apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left 2 (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__exceptionalChartPullback_degree d p v 1 hp))
    · exact (totalDegree_pow _ _).trans
        (Nat.mul_le_mul_left 2 (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__exceptionalChartPullback_degree d q u (-1) hq))

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_mainChartPullback (d : ℕ) (p : PlanePoly) (a k : ℝ)
    (hp : p.totalDegree ≤ d) (z : PachDeZeeuw.Algebraic.Point2) (hs : z 1 ≠ 0) :
    eval (fun i => z i) (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback d p a k) =
      (2 * z 1) ^ d * eval ![a * z 0,
        (z 1 ^ 2 + k * (z 0 ^ 2 - 1)) / (2 * z 1)] p := by
  have hD : eval (fun i => z i) bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartDenominator ≠ 0 := by
    simpa [bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartDenominator] using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hs
  rw [bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_mainChartPullback, eval_planePolynomialRationalPullback d p _ _ _ hp _ hD]
  simp only [bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartDenominator, bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartFirstNumerator, bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartSecondNumerator,
    bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint, map_mul, map_add, map_sub, map_pow, map_one, eval_C, eval_X]
  congr 2
  · field_simp

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_exceptionalChartPullback (d : ℕ) (p : PlanePoly) (a b : ℝ)
    (hp : p.totalDegree ≤ d) (z : PachDeZeeuw.Algebraic.Point2) :
    eval (fun i => z i) (bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback d p a b) =
      eval ![a * z 0, b * z 1] p := by
  rw [bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_exceptionalChartPullback,
    eval_planePolynomialRationalPullback d p _ _ _ hp _ (by simp)]
  simp

private theorem inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__real_sum_squares_zero (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem eval_distanceQuadricMainPolynomial_eq_zero
    (d : ℕ) (p q : PlanePoly) (u v : ℝ)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d)
    (z : PachDeZeeuw.Algebraic.Point2) (hs : z 1 ≠ 0) :
    eval (fun i => z i) (distanceQuadricMainPolynomial d p q u v) = 0 ↔
      eval (fun i => (distanceQuadricChart u v z).1 i) p = 0 ∧
      eval (fun i => (distanceQuadricChart u v z).2 i) q = 0 := by
  rw [distanceQuadricMainPolynomial, map_add, map_pow, map_pow,
    inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__real_sum_squares_zero, inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_mainChartPullback d p _ _ hp z hs,
    inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_mainChartPullback d q _ _ hq z hs]
  have hden : (2 * z 1) ^ d ≠ 0 :=
    pow_ne_zero d (mul_ne_zero (by norm_num) hs)
  simp only [mul_eq_zero, hden, false_or]
  change (eval ![v * z 0, (z 1 ^ 2 + (u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1)) /
      (2 * z 1)] p = 0 ∧
    eval ![u * z 0, (z 1 ^ 2 + -(u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1)) /
      (2 * z 1)] q = 0) ↔ _
  have heq : z 1 ^ 2 + -(u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1) =
      z 1 ^ 2 - (u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1) := by ring
  rw [heq]
  rfl

theorem eval_distanceQuadricExceptionalPolynomial_eq_zero
    (d : ℕ) (p q : PlanePoly) (u v : ℝ)
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) (z : PachDeZeeuw.Algebraic.Point2) :
    eval (fun i => z i) (distanceQuadricExceptionalPolynomial d p q u v) = 0 ↔
      (u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1) = 0 ∧
      eval (fun i => (distanceQuadricExceptionalChart u v z).1 i) p = 0 ∧
      eval (fun i => (distanceQuadricExceptionalChart u v z).2 i) q = 0 := by
  simp only [distanceQuadricExceptionalPolynomial, map_add, map_pow,
    bundle_Esgk_TwoPairDistanceQuadricPolynomialPullback_chartConstraint, map_mul, map_sub, map_one, eval_C, eval_X,
    inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_exceptionalChartPullback d p _ _ hp z,
    inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__eval_exceptionalChartPullback d q _ _ hq z]
  change _ ↔ _ = 0 ∧ eval ![v * z 0, z 1] p = 0 ∧ eval ![u * z 0, -(z 1)] q = 0
  simp only [one_mul, neg_one_mul]
  constructor
  · intro h
    have hfirst : (u ^ 2 - v ^ 2) * (z 0 ^ 2 - 1) = 0 := by
      nlinarith [sq_nonneg (eval ![v * z 0, z 1] p),
        sq_nonneg (eval ![u * z 0, -(z 1)] q)]
    refine ⟨hfirst, ?_⟩
    apply (inline_Esgk_TwoPairDistanceQuadricPolynomialPullback__real_sum_squares_zero _ _).mp
    simpa [hfirst] using h
  · rintro ⟨hfirst, hpz, hqz⟩
    simp [hfirst, hpz, hqz]

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic


theorem circularChartDehomogenization_eq_map_finSuccEquiv (T : CircularChartPoly) :
    circularChartDehomogenization T =
      Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
        (MvPolynomial.finSuccEquiv ℂ 1 T) := by
  let φ : CircularChartPoly →+* Polynomial ℂ :=
    (Polynomial.mapRingHom
      (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))).comp
      (MvPolynomial.finSuccEquiv ℂ 1).toRingEquiv.toRingHom
  change circularChartDehomogenization T = φ T
  congr 1
  dsimp [φ]
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, circularChartDehomogenization,
      MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]
    ·
      simp [RingHom.comp_apply, circularChartDehomogenization,
        MvPolynomial.finSuccEquiv_apply]

 
theorem circularChartDehomogenization_natDegree_le {T : CircularChartPoly} {p : ℕ}
    (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).natDegree ≤ p := by
  rw [circularChartDehomogenization_eq_map_finSuccEquiv]
  calc
    (Polynomial.map (MvPolynomial.eval (fun _ : Fin 1 ↦ (1 : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ 1 T)).natDegree ≤
        (MvPolynomial.finSuccEquiv ℂ 1 T).natDegree := Polynomial.natDegree_map_le
    _ = T.degreeOf 0 := MvPolynomial.natDegree_finSuccEquiv T
    _ ≤ T.totalDegree := MvPolynomial.degreeOf_le_totalDegree T 0
    _ ≤ p := hT.totalDegree_le


theorem circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p) :
    (circularChartDehomogenization T).coeff p = (chartInfinityRestriction T).coeff p := by
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let d : Fin 2 →₀ ℕ := Finsupp.cons p (0 : Fin 1 →₀ ℕ)
  calc
    (circularChartDehomogenization T).coeff p =
        MvPolynomial.coeff d ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      have hd0 : d 0 = p := by simp [d, Finsupp.cons_zero]
      have hd1 : d 1 = 0 := by
        change (Finsupp.cons p (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) = 0
        exact Finsupp.cons_succ (0 : Fin 1) p (0 : Fin 1 →₀ ℕ)
      simp [hd0, hd1]
    _ = MvPolynomial.coeff d T := by rw [hhomogenize]
    _ = (chartInfinityRestriction T).coeff p := by
      rw [chartInfinityRestriction_coeff]

private theorem inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (chartInfinityRestriction T).coeff p ≠ 0 := by
  intro hp
  apply hrestriction
  ext k
  by_cases hkp : k = p
  · simpa [hkp] using hp
  · rw [chartInfinityRestriction_coeff]
    apply hT.coeff_eq_zero
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, Finsupp.cons_zero]
    change k + (Finsupp.cons k (0 : Fin 1 →₀ ℕ)) (Fin.succ 0) ≠ p
    rw [Finsupp.cons_succ, Finsupp.zero_apply, add_zero]
    exact hkp


theorem circularChartDehomogenization_ne_zero_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    circularChartDehomogenization T ≠ 0 := by
  intro hzero
  have hcoeff := inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction
  apply hcoeff
  rw [← circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT, hzero]
  simp


theorem circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    {T : CircularChartPoly} {p : ℕ} (hT : MvPolynomial.IsHomogeneous T p)
    (hrestriction : chartInfinityRestriction T ≠ 0) :
    (circularChartDehomogenization T).natDegree = p := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (circularChartDehomogenization_natDegree_le hT)
  rw [circularChartDehomogenization_coeff_eq_chartInfinityRestriction_coeff hT]
  exact inline_Esgk_CircularTangentDehomogenization__chartInfinityRestriction_coeff_ne_zero_of_isHomogeneous hT hrestriction


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularChartDehomogenization
        (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
          (projectiveCircularChartI (planeHomogenization G.totalDegree G))) ≠ 0 := by
  exact circularChartDehomogenization_ne_zero_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)


theorem IsMaximallyCircular.circularChartDehomogenization_tangentComponent_I_natDegree
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    (circularChartDehomogenization
      (MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
        (projectiveCircularChartI
          (planeHomogenization G.totalDegree G)))).natDegree = planeCircularLocalOrderI G := by
  exact circularChartDehomogenization_natDegree_eq_of_isHomogeneous
    (T := MvPolynomial.homogeneousComponent (planeCircularLocalOrderI G)
      (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (p := planeCircularLocalOrderI G)
    (MvPolynomial.homogeneousComponent_isHomogeneous
      (n := planeCircularLocalOrderI G)
      (φ := projectiveCircularChartI (planeHomogenization G.totalDegree G)))
    (hmax.chartInfinityRestriction_tangentComponent_I_ne_zero hG)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

theorem finite_planeZeroSet_off_polynomial_card_le
    (p q : PlanePoly) (hp : p ≠ 0)
    (hfin : (PlaneCurveZeroSet p \ PlaneCurveZeroSet q).Finite)
    {S : Finset PachDeZeeuw.Algebraic.Point2}
    (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet p \ PlaneCurveZeroSet q) :
    S.card ≤ 4 * p.totalDegree ^ 2 := by
  classical
  let factors : Finset PlanePoly :=
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset
  let fiber : PlanePoly → Finset PachDeZeeuw.Algebraic.Point2 :=
    fun G ↦ S.filter (fun z ↦ z ∈ PlaneCurveZeroSet G)
  have hcover : S ⊆ factors.biUnion fiber := by
    intro z hz
    have hzP : z ∈ PlaneCurveZeroSet p := (hS hz).1
    have hzcover := zeroSet_subset_normalizedFactor_union (p := p) hp hzP
    rcases Set.mem_iUnion.mp hzcover with ⟨G, hzcover⟩
    rcases Set.mem_iUnion.mp hzcover with ⟨hG, hzG⟩
    exact Finset.mem_biUnion.mpr ⟨G, by simpa [factors] using hG,
      Finset.mem_filter.mpr ⟨hz, hzG⟩⟩
  have hfiber : ∀ G ∈ factors,
      (fiber G).card ≤ 4 * G.totalDegree ^ 2 := by
    intro G hG
    have hGmem : G ∈ UniqueFactorizationMonoid.normalizedFactors p := by
      exact UniqueFactorizationMonoid.mem_primeFactors.mp
        (by simpa [factors] using hG)
    have hGirreducible : Irreducible G := normalized_factor_irreducible hGmem
    have hGdvd : G ∣ p :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hGmem
    by_cases hGq : G ∣ q
    · have hfiberEmpty : fiber G = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzG := (Finset.mem_filter.mp hz).2
        exact (hS (Finset.mem_filter.mp hz).1).2
          (PlaneCurveZeroSet_subset_of_dvd hGq hzG)
      simp [hfiberEmpty]
    · have hGdiff :
          (PlaneCurveZeroSet G \ PlaneCurveZeroSet q).Finite :=
        hfin.subset (by
          intro z hz
          exact ⟨PlaneCurveZeroSet_subset_of_dvd hGdvd hz.1, hz.2⟩)
      have hGinter :
          (PlaneCurveZeroSet G ∩ PlaneCurveZeroSet q).Finite := by
        apply Set.not_infinite.mp
        intro hinf
        exact hGq
          (dvd_of_infinite_irreducible_zeroSet_intersection
            hGirreducible hinf)
      have hGzero : (PlaneCurveZeroSet G).Finite := by
        apply (hGdiff.union hGinter).subset
        intro z hz
        by_cases hzq : z ∈ PlaneCurveZeroSet q
        · exact Set.mem_union_right _ ⟨hz, hzq⟩
        · exact Set.mem_union_left _ ⟨hz, hzq⟩
      have hsingular : (SingularPointSet G).Finite := by
        rcases irreducible_has_nonzero_partial G hGirreducible with hpartial | hpartial
        · exact (finite_singularities_of_irreducible_bound
            G hGirreducible le_rfl hpartial).1
        · exact (finite_singularities_of_irreducible_bound
            G hGirreducible le_rfl hpartial).1
      have hzeroSingular : PlaneCurveZeroSet G ⊆ SingularPointSet G :=
        finite_zeroSet_subset_singularities G hGzero
      have hfiberSingular : (fiber G : Set PachDeZeeuw.Algebraic.Point2) ⊆ SingularPointSet G := by
        intro z hz
        exact hzeroSingular (Finset.mem_filter.mp hz).2
      calc
        (fiber G).card = ((fiber G : Set PachDeZeeuw.Algebraic.Point2).ncard) := by simp
        _ ≤ (SingularPointSet G).ncard :=
          Set.ncard_le_ncard hfiberSingular hsingular
        _ ≤ 4 * G.totalDegree ^ 2 :=
          singularPointSet_ncard_le_four_mul_degree_sq_of_irreducible
            G G.totalDegree hGirreducible le_rfl
  have hledger :
      ∑ G ∈ factors, G.totalDegree ≤ p.totalDegree := by
    simpa [factors] using normalizedFactors_toFinset_totalDegree_sum_le p hp
  have hsquares :
      (∑ G ∈ factors, G.totalDegree) ^ 2 ≥
        ∑ G ∈ factors, G.totalDegree ^ 2 := by
    exact Finset.sum_sq_le_sq_sum_of_nonneg (by
      intro G hG
      exact Nat.zero_le _)
  calc
    S.card ≤ (factors.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ G ∈ factors, (fiber G).card := Finset.card_biUnion_le
    _ ≤ ∑ G ∈ factors, 4 * G.totalDegree ^ 2 := by
      exact Finset.sum_le_sum fun G hG ↦ hfiber G hG
    _ = 4 * (∑ G ∈ factors, G.totalDegree ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 4 * (∑ G ∈ factors, G.totalDegree) ^ 2 :=
      Nat.mul_le_mul_left 4 hsquares
    _ ≤ 4 * p.totalDegree ^ 2 := by
      exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hledger 2)


end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open EuclideanGeometry PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem circleEquationPolynomial_totalDegree_eq (c : _root_.Point2) (r : ℝ) :
    (circleEquationPolynomial c r).totalDegree = 2 := by
  apply le_antisymm
  · have hconstant :
        (MvPolynomial.C (r ^ 2) : PlanePoly).totalDegree ≤ 2 := by
      rw [MvPolynomial.totalDegree_C]
      omega
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (planeSquaredDistancePolynomial_totalDegree_le c) hconstant)
  · have htop :
        MvPolynomial.homogeneousComponent 2 (circleEquationPolynomial c r) ≠ 0 := by
      have hconstant :
          MvPolynomial.homogeneousComponent 2
              (MvPolynomial.C (r ^ 2) : PlanePoly) = 0 := by
        apply MvPolynomial.homogeneousComponent_eq_zero
        rw [MvPolynomial.totalDegree_C]
        omega
      rw [circleEquationPolynomial, map_sub,
        homogeneousComponent_two_planeSquaredDistancePolynomial, hconstant, sub_zero]
      exact planeRadialQuadratic_ne_zero
    by_contra hdegree
    apply htop
    apply MvPolynomial.homogeneousComponent_eq_zero
    omega


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

variable {n : ℕ}


theorem IsMaximallyCircular.circularITangentPolynomial_ne_zero
    {G : PlanePoly} (hmax : IsMaximallyCircular G) (hG : G ≠ 0) :
    circularITangentPolynomial G ≠ 0 := by
  exact hmax.circularChartDehomogenization_tangentComponent_I_ne_zero hG


theorem IsMaximallyCircular.circularITangentPolynomial_natDegree
    {G : PlanePoly} {pdeg : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * pdeg) :
    (circularITangentPolynomial G).natDegree = pdeg := by
  have hI := hmax.1
  have hlocal : planeCircularLocalOrderI G = pdeg := by
    omega
  rw [circularITangentPolynomial,
    hmax.circularChartDehomogenization_tangentComponent_I_natDegree hG, hlocal]


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic

theorem finite_plane_chart_cardinality
    (p q : PlanePoly) (hp : p ≠ 0)
    {β : Type*} (f : PachDeZeeuw.Algebraic.Point2 → β) (U : Set β)
    (hU : U.Finite)
    (hmap : f '' (PlaneCurveZeroSet p \ PlaneCurveZeroSet q) ⊆ U)
    (hinj : Set.InjOn f (PlaneCurveZeroSet p \ PlaneCurveZeroSet q)) :
    (PlaneCurveZeroSet p \ PlaneCurveZeroSet q).ncard ≤
        4 * p.totalDegree ^ 2 ∧
      (f '' (PlaneCurveZeroSet p \ PlaneCurveZeroSet q)).ncard ≤
        4 * p.totalDegree ^ 2 := by
  classical
  let A : Set PachDeZeeuw.Algebraic.Point2 := PlaneCurveZeroSet p \ PlaneCurveZeroSet q
  have himage : (f '' A).Finite := hU.subset hmap
  have hA : A.Finite := himage.of_finite_image hinj
  have hS : (hA.toFinset : Set PachDeZeeuw.Algebraic.Point2) ⊆
      PlaneCurveZeroSet p \ PlaneCurveZeroSet q := by
    intro z hz
    exact hA.mem_toFinset.mp hz
  have hcard := finite_planeZeroSet_off_polynomial_card_le p q hp
    hA hS
  have hAcard : A.ncard ≤ 4 * p.totalDegree ^ 2 := by
    rw [Set.ncard_eq_toFinset_card _ hA]
    exact hcard
  constructor
  · exact hAcard
  · rw [hinj.ncard_image]
    exact hAcard

theorem finite_plane_chart_cardinality_of_infinite_off
    (p q : PlanePoly) {β : Type*} (f : PachDeZeeuw.Algebraic.Point2 → β) (U : Set β)
    (hU : U.Finite)
    (hmap : f '' (PlaneCurveZeroSet p \ PlaneCurveZeroSet q) ⊆ U)
    (hinj : Set.InjOn f (PlaneCurveZeroSet p \ PlaneCurveZeroSet q))
    (hinf : (PlaneCurveZeroSet q)ᶜ.Infinite) :
    p ≠ 0 ∧
      (PlaneCurveZeroSet p \ PlaneCurveZeroSet q).ncard ≤
        4 * p.totalDegree ^ 2 ∧
      (f '' (PlaneCurveZeroSet p \ PlaneCurveZeroSet q)).ncard ≤
        4 * p.totalDegree ^ 2 := by
  classical
  let A : Set PachDeZeeuw.Algebraic.Point2 := PlaneCurveZeroSet p \ PlaneCurveZeroSet q
  have himage : (f '' A).Finite := hU.subset hmap
  have hA : A.Finite := himage.of_finite_image hinj
  have hp : p ≠ 0 := by
    intro hp
    apply hinf
    have hAeq : A = (PlaneCurveZeroSet q)ᶜ := by
      ext z
      simp [A, hp, mem_PlaneCurveZeroSet]
    rwa [← hAeq]
  exact ⟨hp, finite_plane_chart_cardinality p q hp f U hU hmap hinj⟩


end Esgk
end

end








section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace MvPolynomial

 
theorem homogeneousComponent_map_star {σ : Type*} (m : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent m (map (starRingEnd ℂ) P) =
      map (starRingEnd ℂ) (homogeneousComponent m P) := by
  ext d
  simp only [coeff_homogeneousComponent, coeff_map]
  split <;> simp_all

end MvPolynomial

namespace Esgk

open PachDeZeeuw.Algebraic _root_.Polynomial

variable {n : ℕ}

 
theorem circularChartDehomogenization_map_star (T : CircularChartPoly) :
    circularChartDehomogenization (MvPolynomial.map (starRingEnd ℂ) T) =
      Polynomial.map (starRingEnd ℂ) (circularChartDehomogenization T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [circularChartDehomogenization]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, hP]
      fin_cases i <;> simp [circularChartDehomogenization]


theorem circularJTangentPolynomial_eq_map_star (G : PlanePoly) :
    circularJTangentPolynomial G =
      Polynomial.map (starRingEnd ℂ) (circularITangentPolynomial G) := by
  rw [circularJTangentPolynomial, circularITangentPolynomial,
    ← planeCircularLocalOrderI_eq_planeCircularLocalOrderJ G,
    ← projectiveCircularChartI_planeHomogenization_map_star G,
    MvPolynomial.homogeneousComponent_map_star,
    circularChartDehomogenization_map_star]


end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic
open IrreduciblePlanePolynomial

private theorem inline_Esgk_NormalizedDistancePairCardinality__xOne_off_infinite :
    (PlaneCurveZeroSet (MvPolynomial.X (1 : Fin 2)))ᶜ.Infinite := by
  let line : ℝ → PachDeZeeuw.Algebraic.Point2 := fun t ↦ WithLp.toLp 2 ![t, 1]
  have hline : Function.Injective line := by
    intro s t hst
    have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hst
    simpa [line] using hcoord
  have hrange : (Set.range line).Infinite :=
    Set.infinite_range_of_injective hline
  refine hrange.mono ?_
  rintro z ⟨t, rfl⟩
  intro hz
  rw [mem_PlaneCurveZeroSet] at hz
  simpa [line] using hz

private theorem inline_Esgk_NormalizedDistancePairCardinality__one_off_infinite :
    (PlaneCurveZeroSet (1 : PlanePoly))ᶜ.Infinite := by
  simpa [PlaneCurveZeroSet] using
    (Set.infinite_univ : (Set.univ : Set PachDeZeeuw.Algebraic.Point2).Infinite)

theorem normalizedDistancePairCommonZeroSet_ncard_le
    (C₁ C₂ : IrreduciblePlanePolynomial ℝ) (u v : ℝ)
    (hv : v ≠ 0) (d : ℕ) (hd : 2 ≤ d)
    (hC₁ : C₁.polynomial.totalDegree ≤ d)
    (hC₂ : C₂.polynomial.totalDegree ≤ d)
    (hfin : (normalizedDistancePairCommonZeroSet C₁ C₂ u v).Finite) :
    (normalizedDistancePairCommonZeroSet C₁ C₂ u v).ncard ≤
      80 * d ^ 2 := by
  classical
  let U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    normalizedDistancePairCommonZeroSet C₁ C₂ u v
  let Pm : PlanePoly :=
    distanceQuadricMainPolynomial d C₁.polynomial C₂.polynomial u v
  let Pe : PlanePoly :=
    distanceQuadricExceptionalPolynomial d C₁.polynomial C₂.polynomial u v
  let Sm : Set PachDeZeeuw.Algebraic.Point2 :=
    PlaneCurveZeroSet Pm \ PlaneCurveZeroSet (MvPolynomial.X (1 : Fin 2))
  let Se : Set PachDeZeeuw.Algebraic.Point2 :=
    PlaneCurveZeroSet Pe \ PlaneCurveZeroSet (1 : PlanePoly)
  let M : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) := distanceQuadricChart u v '' Sm
  let exceptionalImage : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    distanceQuadricExceptionalChart u v '' Se
  have hU : U.Finite := hfin
  have hPmDeg : Pm.totalDegree ≤ 4 * d := by
    exact distanceQuadricMainPolynomial_totalDegree_le d _ _ _ _ hC₁ hC₂
  have hPeDeg : Pe.totalDegree ≤ 2 * d := by
    exact distanceQuadricExceptionalPolynomial_totalDegree_le d _ _ _ _ hd hC₁ hC₂
  have hmainMap : M ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    have hwP : eval (fun i ↦ w i) Pm = 0 := by
      rw [← mem_PlaneCurveZeroSet]
      exact hw.1
    have hwq : w 1 ≠ 0 := by
      intro hwq
      apply hw.2
      rw [mem_PlaneCurveZeroSet]
      simpa using hwq
    have hzero :=
      (eval_distanceQuadricMainPolynomial_eq_zero d
        C₁.polynomial C₂.polynomial u v hC₁ hC₂ w hwq).mp hwP
    have heq := distanceQuadricChart_normalized_equalities
      (u := u) (v := v) hwq
    change
      (distanceQuadricChart u v w).1 ∈ PlaneCurveZeroSet C₁.polynomial ∧
        (distanceQuadricChart u v w).2 ∈ PlaneCurveZeroSet C₂.polynomial ∧
        normalizedLeftValue u (distanceQuadricChart u v w).1 =
          normalizedLeftValue v (distanceQuadricChart u v w).2 ∧
        normalizedRightValue u (distanceQuadricChart u v w).1 =
          normalizedRightValue v (distanceQuadricChart u v w).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_PlaneCurveZeroSet]
      exact hzero.1
    · rw [mem_PlaneCurveZeroSet]
      exact hzero.2
    · exact heq.1
    · exact heq.2
  have hmainInj : Set.InjOn (distanceQuadricChart u v) Sm := by
    apply (distanceQuadricChart_injective hv).mono
    intro z hz
    intro hzq
    apply hz.2
    rw [mem_PlaneCurveZeroSet]
    simpa using hzq
  have hmain := finite_plane_chart_cardinality_of_infinite_off
    Pm (MvPolynomial.X (1 : Fin 2)) (distanceQuadricChart u v) U hU
    hmainMap hmainInj inline_Esgk_NormalizedDistancePairCardinality__xOne_off_infinite
  have hmainCard : M.ncard ≤ 64 * d ^ 2 := by
    calc
      M.ncard ≤ 4 * Pm.totalDegree ^ 2 := hmain.2.2
      _ ≤ 4 * (4 * d) ^ 2 := Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left hPmDeg 2)
      _ = 64 * d ^ 2 := by ring
  have hexMap : exceptionalImage ⊆ U := by
    rintro z ⟨w, hw, rfl⟩
    have hwP : eval (fun i ↦ w i) Pe = 0 := by
      rw [← mem_PlaneCurveZeroSet]
      exact hw.1
    have hzero :=
      (eval_distanceQuadricExceptionalPolynomial_eq_zero d
        C₁.polynomial C₂.polynomial u v hC₁ hC₂ w).mp hwP
    have heq := distanceQuadricExceptionalChart_normalized_iff
      (u := u) (v := v) w
    change
      (distanceQuadricExceptionalChart u v w).1 ∈ PlaneCurveZeroSet C₁.polynomial ∧
        (distanceQuadricExceptionalChart u v w).2 ∈ PlaneCurveZeroSet C₂.polynomial ∧
        normalizedLeftValue u (distanceQuadricExceptionalChart u v w).1 =
          normalizedLeftValue v (distanceQuadricExceptionalChart u v w).2 ∧
        normalizedRightValue u (distanceQuadricExceptionalChart u v w).1 =
          normalizedRightValue v (distanceQuadricExceptionalChart u v w).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mem_PlaneCurveZeroSet]
      exact hzero.2.1
    · rw [mem_PlaneCurveZeroSet]
      exact hzero.2.2
    · exact (heq.mpr hzero.1).1
    · exact (heq.mpr hzero.1).2
  have hexInj : Set.InjOn (distanceQuadricExceptionalChart u v) Se :=
    (distanceQuadricExceptionalChart_injective hv).injOn
  have hex := finite_plane_chart_cardinality_of_infinite_off
    Pe (1 : PlanePoly) (distanceQuadricExceptionalChart u v) U hU
    hexMap hexInj inline_Esgk_NormalizedDistancePairCardinality__one_off_infinite
  have hexCard : exceptionalImage.ncard ≤ 16 * d ^ 2 := by
    calc
      exceptionalImage.ncard ≤ 4 * Pe.totalDegree ^ 2 := hex.2.2
      _ ≤ 4 * (2 * d) ^ 2 := Nat.mul_le_mul_left 4
        (Nat.pow_le_pow_left hPeDeg 2)
      _ = 16 * d ^ 2 := by ring
  have hcover : U ⊆ M ∪ exceptionalImage := by
    intro z hz
    change
      z.1 ∈ PlaneCurveZeroSet C₁.polynomial ∧
        z.2 ∈ PlaneCurveZeroSet C₂.polynomial ∧
        normalizedLeftValue u z.1 = normalizedLeftValue v z.2 ∧
        normalizedRightValue u z.1 = normalizedRightValue v z.2 at hz
    have hz1 := hz.1
    have hz2 := hz.2.1
    rw [mem_PlaneCurveZeroSet] at hz1 hz2
    by_cases hsum : z.1 1 + z.2 1 ≠ 0
    · let w : PachDeZeeuw.Algebraic.Point2 :=
        WithLp.toLp 2 ![z.1 0 / v, z.1 1 + z.2 1]
      have hwchart : distanceQuadricChart u v w = z :=
        distanceQuadricChart_eq_of_normalized_equalities hv hsum hz.2.2.1 hz.2.2.2
      have hws : w 1 ≠ 0 := by simpa [w] using hsum
      have hwsource : w ∈ Sm := by
        refine ⟨?_, ?_⟩
        · rw [mem_PlaneCurveZeroSet]
          apply (eval_distanceQuadricMainPolynomial_eq_zero d
            C₁.polynomial C₂.polynomial u v hC₁ hC₂ w hws).2
          rw [hwchart]
          exact ⟨hz1, hz2⟩
        · intro hwq
          rw [mem_PlaneCurveZeroSet] at hwq
          have : z.1 1 + z.2 1 = 0 := by simpa [w] using hwq
          exact hsum this
      exact Set.mem_union_left _ ⟨w, hwsource, hwchart⟩
    · have hsum' : z.1 1 + z.2 1 = 0 := not_ne_iff.mp hsum
      let w : PachDeZeeuw.Algebraic.Point2 := WithLp.toLp 2 ![z.1 0 / v, z.1 1]
      have hwchart : distanceQuadricExceptionalChart u v w = z :=
        distanceQuadricExceptionalChart_eq_of_normalized_equalities
          hv hsum' hz.2.2.1 hz.2.2.2
      have hwsource : w ∈ Se := by
        refine ⟨?_, ?_⟩
        · rw [mem_PlaneCurveZeroSet]
          apply (eval_distanceQuadricExceptionalPolynomial_eq_zero d
            C₁.polynomial C₂.polynomial u v hC₁ hC₂ w).2
          have hc := (distanceQuadricExceptionalChart_normalized_iff
            (u := u) (v := v) w).mp (by
              rw [hwchart]
              exact ⟨hz.2.2.1, hz.2.2.2⟩)
          rw [hwchart]
          exact ⟨hc, hz1, hz2⟩
        · simp [PlaneCurveZeroSet]
      exact Set.mem_union_right _ ⟨w, hwsource, hwchart⟩
  have hMfin : M.Finite := hU.subset hmainMap
  have hEfin : exceptionalImage.Finite := hU.subset hexMap
  calc
    U.ncard ≤ (M ∪ exceptionalImage).ncard := Set.ncard_le_ncard hcover (hMfin.union hEfin)
    _ ≤ M.ncard + exceptionalImage.ncard := Set.ncard_union_le _ _
    _ ≤ 64 * d ^ 2 + 16 * d ^ 2 := Nat.add_le_add hmainCard hexCard
    _ = 80 * d ^ 2 := by ring

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open _root_.Polynomial
open PachDeZeeuw.Algebraic


theorem exists_simultaneously_centered_circular_tangent_polynomials
    {G : PlanePoly} {p : ℕ}
    (hI : circularITangentPolynomial G ≠ 0)
    (hdegree : (circularITangentPolynomial G).natDegree = p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ : ℂ,
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p ∧
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p := by
  obtain ⟨τ, hfactor⟩ :=
    Polynomial.exists_eq_C_leadingCoeff_mul_X_sub_C_pow_natDegree_of_roots_toFinset_card_eq_one
      (circularITangentPolynomial G) hI hroots
  refine ⟨-Complex.I * τ, ?_, ?_⟩
  · nth_rewrite 1 [hfactor]
    rw [hdegree]
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hshift : Complex.I * (-Complex.I * τ) = τ := by
      calc
        Complex.I * (-Complex.I * τ) = -(Complex.I * Complex.I) * τ := by ring
        _ = τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    ring
  · rw [circularJTangentPolynomial_eq_map_star]
    nth_rewrite 1 [hfactor]
    rw [hdegree, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
      Polynomial.sub_comp, Polynomial.X_comp]
    have hshift : -Complex.I * star (-Complex.I * τ) = star τ := by
      have hconj : star (-Complex.I * τ) = Complex.I * star τ := by
        simp
      rw [hconj]
      calc
        -Complex.I * (Complex.I * star τ) =
            -(Complex.I * Complex.I) * star τ := by ring
        _ = star τ := by rw [Complex.I_mul_I]; ring
    rw [hshift]
    simp only [Polynomial.map_C, starRingEnd_apply]
    rw [Polynomial.C_comp]
    ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two :
    (MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2 = 1 := by
  change MvPolynomial.C (1 / 2 : ℂ) * MvPolynomial.C (2 : ℂ) = MvPolynomial.C 1
  rw [← map_mul]
  norm_num

private theorem inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq :
    (MvPolynomial.C Complex.I : CircularChartPoly) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartI G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartI G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartIForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartI, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex
    (G : PlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) =
      affineCircularChartJ G := by
  change
    (((bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces.comp planeToIsotropicCoordinates).comp
      realToComplexPlanePolynomial) G) = affineCircularChartJ G
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
      realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicAffineCircularChartJForFaces, planeToIsotropicCoordinates,
        realToComplexPlanePolynomial, affineCircularChartJ, affineCircularChart,
        circularChartU]
    · simpa [mul_assoc] using inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two
    · calc
        _ = (-MvPolynomial.C Complex.I + circularChartU) *
            ((MvPolynomial.C (1 / 2 : ℂ) : CircularChartPoly) * 2) := by
          simp only [circularChartU]
          ring_nf
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_I_sq]
          ring
        _ = -MvPolynomial.C Complex.I + circularChartU := by
          rw [inline_Esgk_CircularTangentIsotropicFaces__circularChart_C_half_mul_two, mul_one]

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
    {d : ℕ} {P : ComplexPlanePoly} (hP : P.IsHomogeneous d) :
    (planeToIsotropicCoordinates P).IsHomogeneous d := by
  change
    (MvPolynomial.eval₂ (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
      ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
        MvPolynomial.C (1 / (2 * Complex.I)) *
          (MvPolynomial.X 0 - MvPolynomial.X 1)] P).IsHomogeneous d
  have h := hP.eval₂
    (MvPolynomial.C : ℂ →+* ComplexPlanePoly)
    ![MvPolynomial.C (1 / 2 : ℂ) * (MvPolynomial.X 0 + MvPolynomial.X 1),
      MvPolynomial.C (1 / (2 * Complex.I)) *
        (MvPolynomial.X 0 - MvPolynomial.X 1)]
    (fun c ↦ MvPolynomial.isHomogeneous_C (Fin 2) c)
    (fun i ↦ by
      fin_cases i
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).add
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _
      · exact ((MvPolynomial.isHomogeneous_X ℂ 0).sub
          (MvPolynomial.isHomogeneous_X ℂ 1)).C_mul _)
  rw [Nat.one_mul] at h
  exact h

private theorem inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces
    (d : ℕ) (P : ComplexPlanePoly) :
    planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) =
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) := by
  classical
  by_cases hd : d ≤ P.totalDegree
  · have hsum :
        ∑ k ∈ Finset.range (P.totalDegree + 1),
            planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P) =
          planeToIsotropicCoordinates P := by
      rw [← map_sum, MvPolynomial.sum_homogeneousComponent]
    have himage (k : ℕ) :
        (planeToIsotropicCoordinates
          (MvPolynomial.homogeneousComponent k P)).IsHomogeneous k :=
      inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_isHomogeneousForFaces
        (MvPolynomial.homogeneousComponent_isHomogeneous k P)
    symm
    calc
      MvPolynomial.homogeneousComponent d (planeToIsotropicCoordinates P) =
          MvPolynomial.homogeneousComponent d
            (∑ k ∈ Finset.range (P.totalDegree + 1),
              planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        rw [hsum]
      _ = ∑ k ∈ Finset.range (P.totalDegree + 1),
          MvPolynomial.homogeneousComponent d
            (planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent k P)) := by
        simp only [map_sum]
      _ = planeToIsotropicCoordinates (MvPolynomial.homogeneousComponent d P) := by
        simp_rw [MvPolynomial.homogeneousComponent_of_mem (himage _)]
        simp [hd]
  · have hPd : P.totalDegree < d := by omega
    have hTd : (planeToIsotropicCoordinates P).totalDegree < d := by
      rw [planeToIsotropicCoordinates_totalDegree]
      exact hPd
    rw [MvPolynomial.homogeneousComponent_eq_zero d P hPd, map_zero,
      MvPolynomial.homogeneousComponent_eq_zero d _ hTd]

private theorem inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces
    (d : ℕ) (G : PlanePoly) :
    realToComplexPlanePolynomial (MvPolynomial.homogeneousComponent d G) =
      MvPolynomial.homogeneousComponent d (realToComplexPlanePolynomial G) := by
  ext e
  simp only [realToComplexPlanePolynomial, MvPolynomial.coeff_map,
    MvPolynomial.coeff_homogeneousComponent]
  split_ifs <;> simp


private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartI (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartI, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartI (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartIForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]

private theorem inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces
    (D : ℕ) (G : PlanePoly) :
    projectiveCircularChartJ (planeHomogenization D G) =
      bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D
        (planeToIsotropicCoordinates (realToComplexPlanePolynomial G)) := by
  rw [projectiveCircularChartJ, projectiveCircularChart_planeHomogenization]
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  change affineCircularChartJ (MvPolynomial.homogeneousComponent d G) = _
  rw [← inline_Esgk_CircularTangentIsotropicFaces__isotropicAffineCircularChartJForFaces_planeToIsotropic_realToComplex]
  congr 1
  rw [inline_Esgk_CircularTangentIsotropicFaces__realToComplexPlanePolynomial_homogeneousComponentForFaces,
    inline_Esgk_CircularTangentIsotropicFaces__planeToIsotropicCoordinates_homogeneousComponentForFaces]


@[simp]
theorem isotropicFaceExponent_zero (a b : ℕ) : isotropicFaceExponent a b 0 = a := by
  simp [isotropicFaceExponent]

@[simp]
theorem isotropicFaceExponent_one (a b : ℕ) : isotropicFaceExponent a b 1 = b := by
  simp [isotropicFaceExponent]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff {a b c d : ℕ} :
    isotropicFaceExponent a b = isotropicFaceExponent c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff {e : Fin 2 →₀ ℕ} {a b : ℕ} :
    e = isotropicFaceExponent a b ↔ e 0 = a ∧ e 1 = b := by
  constructor
  · intro h
    exact ⟨by simpa using DFunLike.congr_fun h 0,
      by simpa using DFunLike.congr_fun h 1⟩
  · rintro ⟨hzero, hone⟩
    apply Finsupp.ext
    intro i
    fin_cases i
    · simp [hzero]
    · simp [hone]


theorem circularChartDehomogenization_homogeneousComponent_coeff
    (F : CircularChartPoly) (p a : ℕ) (ha : a ≤ p) :
    (circularChartDehomogenization (MvPolynomial.homogeneousComponent p F)).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a (p - a)) F := by
  let T := MvPolynomial.homogeneousComponent p F
  have hT : MvPolynomial.IsHomogeneous T p :=
    MvPolynomial.homogeneousComponent_isHomogeneous p F
  have hhomogenize : (circularChartDehomogenization T).homogenize p = T := by
    apply Polynomial.homogenize_eq_of_isHomogeneous hT
    rfl
  let e := isotropicFaceExponent a (p - a)
  calc
    (circularChartDehomogenization T).coeff a =
        MvPolynomial.coeff e ((circularChartDehomogenization T).homogenize p) := by
      rw [Polynomial.coeff_homogenize]
      simp [e, Nat.add_sub_of_le ha]
    _ = MvPolynomial.coeff e T := by rw [hhomogenize]
    _ = MvPolynomial.coeff e F := by
      have hedegree : Finsupp.degree e = p := by
        rw [Finsupp.degree_eq_sum]
        simp [e, Fin.sum_univ_two, Nat.add_sub_of_le ha]
      rw [MvPolynomial.coeff_homogeneousComponent, if_pos hedegree]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial
    (P : Polynomial ℂ) (a b k : ℕ) :
    MvPolynomial.coeff (isotropicFaceExponent a b)
        (circularChartZ ^ k * Polynomial.toMvPolynomial 0 P) =
      if b = k then P.coeff a else 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, mul_add, MvPolynomial.coeff_add, Polynomial.coeff_add, hP, hQ]
      by_cases hbk : b = k <;> simp [hbk]
  | monomial n c =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial]
      simp only [map_mul, Polynomial.toMvPolynomial_C, map_pow,
        Polynomial.toMvPolynomial_X]
      have hpoly :
          circularChartZ ^ k *
              ((MvPolynomial.C c : CircularChartPoly) * MvPolynomial.X 0 ^ n) =
            MvPolynomial.monomial (isotropicFaceExponent n k) c := by
        rw [MvPolynomial.monomial_eq]
        simp [isotropicFaceExponent, Finsupp.prod_fintype, Fin.prod_univ_two,
          circularChartZ]
        ring
      rw [hpoly, MvPolynomial.coeff_monomial]
      simp only [inline_Esgk_CircularTangentIsotropicFaces__isotropicFaceExponent_eq_iff, Polynomial.coeff_C_mul_X_pow]
      by_cases hbk : b = k
      · subst b
        by_cases han : a = n
        · subst a
          simp
        · simp [han, Ne.symm han]
      · have hkb : k ≠ b := Ne.symm hbk
        by_cases han : a = n
        · subst a
          simp [hbk, hkb]
        · simp [hbk, hkb, Ne.symm han]

private theorem inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces
    (D : ℕ) (Q : ComplexPlanePoly) (A B : CircularChartPoly)
    (hdegree : Q.totalDegree ≤ D) :
    (∑ d ∈ Finset.range (D + 1),
      circularChartZ ^ (D - d) *
        MvPolynomial.eval₂Hom (MvPolynomial.C : ℂ →+* CircularChartPoly) ![A, B]
          (MvPolynomial.homogeneousComponent d Q)) =
      ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
  classical
  calc
    _ = ∑ d ∈ Finset.range (D + 1),
        ∑ e ∈ Q.support with e.degree = d,
          MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
            circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [MvPolynomial.homogeneousComponent_apply, map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hedegree : e.degree = d := (Finset.mem_filter.mp he).2
      rw [MvPolynomial.eval₂Hom_monomial]
      rw [hedegree]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two]
      ring
    _ = ∑ e ∈ Q.support,
        MvPolynomial.C (MvPolynomial.coeff e Q) * A ^ e 0 * B ^ e 1 *
          circularChartZ ^ (D - e.degree) := by
      apply Finset.sum_fiberwise_of_maps_to
      intro e he
      rw [Finsupp.degree_eq_sum]
      simp only [Finset.mem_range, Nat.lt_add_one_iff]
      calc
        ∑ i, e i = e.sum (fun _ a ↦ a) :=
          (Finsupp.sum_fintype e (fun _ a ↦ a) (fun _ ↦ rfl)).symm
        _ ≤ D := (MvPolynomial.le_totalDegree he).trans hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum
    (D : ℕ) (Q : ComplexPlanePoly) (hdegree : Q.totalDegree ≤ D) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces D Q =
      ∑ e ∈ Q.support,
        bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e (MvPolynomial.coeff e Q) := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__homogenized_eval₂_eq_support_sumForFaces D Q _ _ hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial
    (D : ℕ) (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces D e c =
      circularChartZ ^ (D - e.degree) *
        Polynomial.toMvPolynomial 0 (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c) := by
  simp [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces, bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces,
    circularChartU, map_ofNat]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces (e : Fin 2 →₀ ℕ) :
    e.degree = e 0 + e 1 := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_two]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces e c =
      Polynomial.C (c * Complex.I ^ e 0) * Polynomial.X ^ e 0 *
        (2 - Polynomial.C Complex.I * Polynomial.X) ^ e 1 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartIPolynomialForFaces, mul_pow, ← map_pow, map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq
    (e : Fin 2 →₀ ℕ) (c : ℂ) :
    bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces e c =
      Polynomial.C (c * (-Complex.I) ^ e 1) * Polynomial.X ^ e 1 *
        (2 + Polynomial.C Complex.I * Polynomial.X) ^ e 0 := by
  rw [bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJPolynomialForFaces, mul_pow, ← map_neg, ← map_pow,
    map_mul]
  ring

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face
    (p a : ℕ) (ha : a ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartITermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent a p
      then c * Complex.I ^ a * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - a = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + a := by omega
    have hae : a ≤ e 0 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartIPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent a p
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 0 ≠ a := by
        intro hezero
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · simp [hezero]
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
      have hlt : a < e 0 := lt_of_le_of_ne hae (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face
    (p b : ℕ) (hb : b ≤ p) (e : Fin 2 →₀ ℕ) (c : ℂ)
    (hebound : e 0 ≤ p ∧ e 1 ≤ p) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicCircularChartJTermForFaces (2 * p) e c) =
      if e = isotropicFaceExponent p b
      then c * (-Complex.I) ^ b * (2 : ℂ) ^ p
      else 0 := by
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_eq_toMvPolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__coeff_circularChartZ_pow_mul_toMvPolynomial]
  by_cases hz : p - b = 2 * p - e.degree
  · rw [if_pos hz]
    have hedegree_le : e.degree ≤ 2 * p := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
      omega
    have hedegree : e.degree = p + b := by omega
    have hbe : b ≤ e 1 := by
      rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
      omega
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJPolynomialForFaces_eq]
    by_cases he : e = isotropicFaceExponent p b
    · subst e
      simp only [isotropicFaceExponent_zero, isotropicFaceExponent_one]
      simp only [if_true]
      rw [mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      simp [Polynomial.coeff_zero_eq_eval_zero]
    · rw [if_neg he, mul_assoc, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow_mul']
      have hene : e 1 ≠ b := by
        intro heone
        apply he
        apply Finsupp.ext
        intro i
        fin_cases i
        · rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces] at hedegree
          simp
          omega
        · simp [heone]
      have hlt : b < e 1 := lt_of_le_of_ne hbe (Ne.symm hene)
      simp [not_le.mpr hlt]
  · rw [if_neg hz, if_neg]
    intro he
    subst e
    apply hz
    rw [inline_Esgk_CircularTangentIsotropicFaces__finTwo_degree_eq_addForFaces]
    simp
    omega

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face
    (Q : ComplexPlanePoly) (p a : ℕ) (ha : a ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent a (p - a))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartIForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent a p ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent a p)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent a p) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartITermForFaces_coeff_face p a ha _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face
    (Q : ComplexPlanePoly) (p b : ℕ) (hb : b ≤ p) (hbound : BidegreeBound p Q) :
    MvPolynomial.coeff (isotropicFaceExponent b (p - b))
        (bundle_Esgk_CircularTangentIsotropicFaces_isotropicHomogenizedCircularChartJForFaces (2 * p) Q) =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  classical
  have hdegree : Q.totalDegree ≤ 2 * p :=
    totalDegree_le_two_mul_of_bidegreeBound p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_eq_support_sum _ _ hdegree]
  rw [MvPolynomial.coeff_sum]
  by_cases he : isotropicFaceExponent p b ∈ Q.support
  · rw [Finset.sum_eq_single (isotropicFaceExponent p b)]
    · rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ he),
        if_pos rfl]
      ring
    · intro e heQ hne
      rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
        if_neg hne]
    · intro hnot
      exact (hnot he).elim
  · have hcoeff : MvPolynomial.coeff (isotropicFaceExponent p b) Q = 0 := by
      rwa [← MvPolynomial.notMem_support_iff]
    rw [hcoeff, mul_zero]
    apply Finset.sum_eq_zero
    intro e heQ
    rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicCircularChartJTermForFaces_coeff_face p b hb _ _ (hbound _ heQ),
      if_neg]
    intro heq
    subst e
    exact he heQ


theorem circularITangentPolynomial_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (ha : a ≤ p) :
    (circularITangentPolynomial G).coeff a =
      (2 : ℂ) ^ p * Complex.I ^ a *
        MvPolynomial.coeff (isotropicFaceExponent a p)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  rw [circularITangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p a ha,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartI_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartIForFaces_coeff_face _ p a ha hbound


theorem circularJTangentPolynomial_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))
    (hb : b ≤ p) :
    (circularJTangentPolynomial G).coeff b =
      (2 : ℂ) ^ p * (-Complex.I) ^ b *
        MvPolynomial.coeff (isotropicFaceExponent p b)
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) := by
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  rw [circularJTangentPolynomial, hlocal,
    circularChartDehomogenization_homogeneousComponent_coeff _ p b hb,
    hdegree, inline_Esgk_CircularTangentIsotropicFaces__projectiveCircularChartJ_planeHomogenization_eq_isotropicForFaces]
  exact inline_Esgk_CircularTangentIsotropicFaces__isotropicHomogenizedCircularChartJForFaces_coeff_face _ p b hb hbound


private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).coeff b).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [← map_pow, Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hone, Ne.symm hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]

private theorem inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial
    (Q : ComplexPlanePoly) (a b : ℕ) :
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).coeff a).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent a b) Q := by
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ]
  | monomial e c =>
      rw [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, MvPolynomial.eval₂Hom_monomial]
      simp [Finsupp.prod_fintype, Fin.prod_univ_two, MvPolynomial.coeff_monomial]
      rw [mul_comm (Polynomial.X ^ e 0), ← map_pow,
        Polynomial.coeff_C_mul_X_pow]
      by_cases hzero : e 0 = a
      · subst a
        by_cases hone : e 1 = b
        · subst b
          simp [inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hone, Ne.symm hone, inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
      · have hzero' : a ≠ e 0 := Ne.symm hzero
        by_cases hone : e 1 = b
        · subst b
          simp [hzero, hzero', inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]
        · simp [hzero, hzero', hone,
            inline_Esgk_CircularTangentIsotropicFaces__eq_isotropicFaceExponent_iff]


@[simp]
theorem isotropicSecondFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (a : ℕ) :
    (isotropicSecondFacePolynomial p Q).coeff a =
      MvPolynomial.coeff (isotropicFaceExponent a p) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial Q a p

@[simp]
theorem isotropicFirstFacePolynomial_coeff (p : ℕ) (Q : ComplexPlanePoly) (b : ℕ) :
    (isotropicFirstFacePolynomial p Q).coeff b =
      MvPolynomial.coeff (isotropicFaceExponent p b) Q := by
  exact inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial Q p b

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le
    {R : Type*} [CommSemiring R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X + Polynomial.C r)).coeff p = P.coeff p := by
  rw [← Polynomial.taylor_apply]
  by_cases hdeg : P.natDegree = p
  · subst p
    rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]
  · have hlt : P.natDegree < p := lt_of_le_of_ne hdegree hdeg
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    simpa using hlt

private theorem inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le
    {R : Type*} [CommRing R] [Nontrivial R]
    (P : Polynomial R) (r : R) {p : ℕ} (hdegree : P.natDegree ≤ p) :
    (P.comp (Polynomial.X - Polynomial.C r)).coeff p = P.coeff p := by
  simpa [sub_eq_add_neg] using
    inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_add_C_of_natDegree_le P (-r) hdegree


private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_secondVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation
    (c : ℂ) (Q : ComplexPlanePoly) :
    bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial (isotropicTranslation c Q) =
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q) := by
  change
    ((bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial.comp (isotropicTranslation c)) Q) =
      (((bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation c).comp
        bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial) Q)
  apply RingHom.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
      bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]
  · intro i
    fin_cases i <;>
      simp [bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial, isotropicTranslation,
        bundle_Esgk_CircularTangentIsotropicFaces_firstVariableIteratedTranslation, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  ext a
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsSecondVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  ext b
  rw [Polynomial.coeff_zero, inline_Esgk_CircularTangentIsotropicFaces__coeff_coeff_bivariateAsFirstVariablePolynomial]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle


theorem isotropicSecondFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicSecondFacePolynomial p (isotropicTranslation c Q) =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
  rw [isotropicSecondFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsSecondVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation c) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsSecondVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C (star c)))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicSecondFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]


theorem isotropicFirstFacePolynomial_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly} (hbound : BidegreeBound p Q) :
    isotropicFirstFacePolynomial p (isotropicTranslation c Q) =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
  rw [isotropicFirstFacePolynomial,
    inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_isotropicTranslation]
  let R := bundle_Esgk_CircularTangentIsotropicFaces_bivariateAsFirstVariablePolynomial Q
  let S := Polynomial.map (bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation (star c)) R
  have hR : R.natDegree ≤ p := inline_Esgk_CircularTangentIsotropicFaces__bivariateAsFirstVariablePolynomial_natDegree_le hbound
  have hS : S.natDegree ≤ p := Polynomial.natDegree_map_le.trans hR
  change
    (S.comp (Polynomial.X - Polynomial.C (Polynomial.C c))).coeff p = _
  rw [inline_Esgk_CircularTangentIsotropicFaces__polynomial_coeff_comp_X_sub_C_of_natDegree_le S _ hS]
  simp [S, R, isotropicFirstFacePolynomial, bundle_Esgk_CircularTangentIsotropicFaces_polynomialTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicSecondFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [isotropicSecondFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).1
  simp only [isotropicFaceExponent_zero] at hle
  exact (not_le_of_gt ha) hle

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le
    {Q : ComplexPlanePoly} {p : ℕ} (hbound : BidegreeBound p Q) :
    (isotropicFirstFacePolynomial p Q).natDegree ≤ p := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro b hb
  rw [isotropicFirstFacePolynomial_coeff]
  rw [← MvPolynomial.notMem_support_iff]
  intro he
  have hle := (hbound _ he).2
  simp only [isotropicFaceExponent_one] at hle
  exact (not_le_of_gt hb) hle


theorem circularITangentPolynomial_eq_isotropicSecondFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularITangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicSecondFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderI G = p := by
    have hI := hmax.1
    omega
  have hTdegree : (circularITangentPolynomial G).natDegree ≤ p := by
    rw [circularITangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartI (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicSecondFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicSecondFacePolynomial_natDegree_le hbound
  ext a
  by_cases ha : a ≤ p
  · rw [circularITangentPolynomial_coeff_eq_isotropic_second_face hmax hdegree hbound ha,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicSecondFacePolynomial_coeff]
    ring
  · have hpa : p < a := lt_of_not_ge ha
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpa),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpa)]
    simp


theorem circularJTangentPolynomial_eq_isotropicFirstFace
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) :
    circularJTangentPolynomial G =
      Polynomial.C ((2 : ℂ) ^ p) *
        (isotropicFirstFacePolynomial p
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hlocal : planeCircularLocalOrderJ G = p := by
    have hJ := hmax.2
    omega
  have hTdegree : (circularJTangentPolynomial G).natDegree ≤ p := by
    rw [circularJTangentPolynomial, hlocal]
    exact circularChartDehomogenization_natDegree_le
      (MvPolynomial.homogeneousComponent_isHomogeneous p
        (projectiveCircularChartJ (planeHomogenization G.totalDegree G)))
  have hFdegree : (isotropicFirstFacePolynomial p Q).natDegree ≤ p :=
    inline_Esgk_CircularTangentIsotropicFaces__isotropicFirstFacePolynomial_natDegree_le hbound
  ext b
  by_cases hb : b ≤ p
  · rw [circularJTangentPolynomial_coeff_eq_isotropic_first_face hmax hdegree hbound hb,
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      isotropicFirstFacePolynomial_coeff]
    ring
  · have hpb : p < b := lt_of_not_ge hb
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hTdegree.trans_lt hpb),
      Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hFdegree.trans_lt hpb)]
    simp

private theorem inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation (c : ℂ) :
    isotropicTranslation (-c) = inverseIsotropicTranslation c := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    fin_cases i <;>
      simp [isotropicTranslation, inverseIsotropicTranslation]

private theorem inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation
    (c : ℂ) (p : ℕ) {Q : ComplexPlanePoly}
    (hbound : BidegreeBound p (isotropicTranslation c Q)) :
    BidegreeBound p Q := by
  have hneg := bidegreeBound_isotropicTranslation (-c) p hbound
  rw [inline_Esgk_CircularTangentIsotropicFaces__isotropicTranslation_neg_eq_inverseIsotropicTranslation] at hneg
  have hinv : inverseIsotropicTranslation c (isotropicTranslation c Q) = Q := by
    simpa [RingHom.comp_apply] using
      RingHom.congr_fun (inverseIsotropicTranslation_comp_isotropicTranslation c) Q
  rw [hinv] at hneg
  exact hneg


theorem circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
    {G : PlanePoly} {p a : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularITangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (Complex.I * c))).coeff a =
        (2 : ℂ) ^ p * Complex.I ^ a *
          MvPolynomial.coeff (isotropicFaceExponent a p)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicSecondFacePolynomial p Qc =
      (isotropicSecondFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C c) := by
    simpa [Qc, Q] using isotropicSecondFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularITangentPolynomial_eq_isotropicSecondFace hmax hdegree hboundQ
  have hpoly :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicSecondFacePolynomial p Qc).comp
            (Polynomial.C Complex.I * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicSecondFacePolynomial_coeff]
  ring


theorem circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
    {G : PlanePoly} {p b : ℕ} (c : ℂ) (hmax : IsMaximallyCircular G)
    (hdegree : G.totalDegree = 2 * p)
    (hbound : BidegreeBound p
      (isotropicTranslationEquiv c
        (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) :
    ((circularJTangentPolynomial G).comp
      (Polynomial.X + Polynomial.C (-Complex.I * star c))).coeff b =
        (2 : ℂ) ^ p * (-Complex.I) ^ b *
          MvPolynomial.coeff (isotropicFaceExponent p b)
            (isotropicTranslationEquiv c
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G))) := by
  let Q := planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  let Qc := isotropicTranslationEquiv c Q
  have hboundQ : BidegreeBound p Q := by
    apply inline_Esgk_CircularTangentIsotropicFaces__bidegreeBound_of_isotropicTranslation c p
    simpa [Q, Qc] using hbound
  have hface : isotropicFirstFacePolynomial p Qc =
      (isotropicFirstFacePolynomial p Q).comp
        (Polynomial.X - Polynomial.C (star c)) := by
    simpa [Qc, Q] using isotropicFirstFacePolynomial_isotropicTranslation c p hboundQ
  have hbase := circularJTangentPolynomial_eq_isotropicFirstFace hmax hdegree hboundQ
  have hpoly :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star c)) =
        Polynomial.C ((2 : ℂ) ^ p) *
          (isotropicFirstFacePolynomial p Qc).comp
            (Polynomial.C (-Complex.I) * Polynomial.X) := by
    rw [hbase]
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.comp_assoc]
    rw [hface, Polynomial.comp_assoc]
    congr 2
    simp
    ring_nf
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
    ring
  rw [hpoly, Polynomial.coeff_C_mul, Polynomial.comp_C_mul_X_coeff,
    isotropicFirstFacePolynomial_coeff]
  ring

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry PachDeZeeuw




 


 
theorem perpendicularBisectorDirection_ne_zero
    {x z : PachDeZeeuw.Algebraic.Point2} (hxz : x ≠ z) :
    perpendicularBisectorDirection x z ≠ 0 := by
  intro hzero
  apply hxz
  ext i
  fin_cases i
  · have hcoord := congrArg (fun w : PachDeZeeuw.Algebraic.Point2 ↦ w 1) hzero
    simp [perpendicularBisectorDirection] at hcoord
    simpa using (sub_eq_zero.mp hcoord).symm
  · have hcoord := congrArg (fun w : PachDeZeeuw.Algebraic.Point2 ↦ w 0) hzero
    simp [perpendicularBisectorDirection] at hcoord
    simpa using sub_eq_zero.mp hcoord


theorem CurveSymmetries.affineLine_not_subset
    {d : ℕ} {C : Set CurveSymmetries.Point2}
    (hcurve : CurveSymmetries.IsIrreducibleCurve d C)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle C)
    {x v : CurveSymmetries.Point2} (hv : v ≠ 0) :
    ¬ PachDeZeeuw.Algebraic.PlaneCurveZeroSet
        (affineLinePolynomial x v) ⊆ C := by
  intro hsubset
  obtain ⟨p, _hp0, hpirreducible, hC, hpdivides⟩ :=
    CurveSymmetries.dvd_affineLinePolynomial_of_translationOrbit
      hcurve hv (fun n ↦ hsubset (by
        change MvPolynomial.eval
            (fun i ↦ (x + (n : ℝ) • v) i)
            (affineLinePolynomial x v) = 0
        rw [affineLinePolynomial_eval]
        change v 1 * (x 0 + (n : ℝ) * v 0 - x 0) -
          v 0 * (x 1 + (n : ℝ) * v 1 - x 1) = 0
        ring))
  have hlineIrreducible : Irreducible (affineLinePolynomial x v) :=
    affineLinePolynomial_irreducible hv
  have hassociated : Associated p (affineLinePolynomial x v) :=
    hpirreducible.associated_of_dvd hlineIrreducible hpdivides
  have hzeroSets :
      PachDeZeeuw.Algebraic.PlaneCurveZeroSet p =
        PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x v) :=
    zeroSet_eq_of_associated hassociated
  have hcarrierLine : C =
      {z : CurveSymmetries.Point2 |
        v 1 * z 0 + (-v 0) * z 1 = v 1 * x 0 - v 0 * x 1} := by
    calc
      C = CurveSymmetries.PlaneCurveZeroSet p := hC
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet p := by rfl
      _ = PachDeZeeuw.Algebraic.PlaneCurveZeroSet
          (affineLinePolynomial x v) := hzeroSets
      _ = {z : CurveSymmetries.Point2 |
          v 1 * z 0 + (-v 0) * z 1 =
            v 1 * x 0 - v 0 * x 1} :=
        affineLinePolynomial_zeroSet_eq_line x v
  apply hnot
  exact Or.inl ⟨v 1, -v 0, v 1 * x 0 - v 0 * x 1,
    affineLinePolynomial_direction_ne_zero hv, hcarrierLine⟩




end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 as described in the repository LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw (PreparedBipartiteInput Point4)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet SingularPointSet)


@[simp]
theorem preparedSecondCurveIrreducible_polynomial
    {d : ℕ} (X : PreparedBipartiteInput d) :
    (preparedSecondCurveIrreducible X).polynomial = preparedSecondCurvePolynomial X := rfl







end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


theorem IsMaximallyCircular.centered_isotropic_corner_normal_form_of_tangent_identities
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p) (ξ : ℂ)
    (hcenterI :
      (circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ)) =
        Polynomial.C (circularITangentPolynomial G).leadingCoeff * Polynomial.X ^ p)
    (hcenterJ :
      (circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ)) =
        Polynomial.C (star (circularITangentPolynomial G).leadingCoeff) *
          Polynomial.X ^ p) :
    ∃ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  let Q : ComplexPlanePoly :=
    planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  let Qc : ComplexPlanePoly := isotropicTranslationEquiv ξ Q
  have hboundQ : BidegreeBound p Q := by
    simpa only [Q] using
      hmax.bidegreeBound_planeIsotropicCoordinateEquiv hG p hdegree
  have hbound : BidegreeBound p Qc := by
    simpa only [Qc, isotropicTranslationEquiv_apply] using
      bidegreeBound_isotropicTranslation ξ p hboundQ
  have hrow : ∀ a < p, MvPolynomial.coeff (isotropicFaceExponent a p) Qc = 0 := by
    intro a ha
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff a = 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt ha]
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := a) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * Complex.I ^ a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ Complex.I_ne_zero)
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcolumn : ∀ b < p, MvPolynomial.coeff (isotropicFaceExponent p b) Qc = 0 := by
    intro b hb
    have hcenterCoeff :
        ((circularJTangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (-Complex.I * star ξ))).coeff b = 0 := by
      rw [hcenterJ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      simp [ne_of_lt hb]
    have hface :=
      circularJTangentPolynomial_comp_centered_coeff_eq_isotropic_first_face
        (G := G) (p := p) (b := b) ξ hmax hdegree hbound
    rw [hcenterCoeff] at hface
    have hscalar : (2 : ℂ) ^ p * (-Complex.I) ^ b ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num))
        (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
    exact (mul_eq_zero.mp hface.symm).resolve_left hscalar
  have hcorner : MvPolynomial.coeff (bivariateCornerExponent p) Qc ≠ 0 := by
    have hcenterCoeff :
        ((circularITangentPolynomial G).comp
          (Polynomial.X + Polynomial.C (Complex.I * ξ))).coeff p ≠ 0 := by
      rw [hcenterI, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
      exact Polynomial.leadingCoeff_ne_zero.mpr hI
    have hface :=
      circularITangentPolynomial_comp_centered_coeff_eq_isotropic_second_face
        (G := G) (p := p) (a := p) ξ hmax hdegree hbound
    have hproduct :
        (2 : ℂ) ^ p * Complex.I ^ p *
          MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 := by
      rw [← hface]
      exact hcenterCoeff
    have hcornerFace : MvPolynomial.coeff (isotropicFaceExponent p p) Qc ≠ 0 :=
      (mul_ne_zero_iff.mp hproduct).2
    simpa only [bivariateCornerExponent, isotropicFaceExponent] using hcornerFace
  have htotal : Qc.totalDegree = 2 * p := by
    apply Nat.le_antisymm (totalDegree_le_two_mul_of_bidegreeBound p hbound)
    have hmem : bivariateCornerExponent p ∈ Qc.support :=
      MvPolynomial.mem_support_iff.mpr hcorner
    have hle := MvPolynomial.le_totalDegree hmem
    simpa [bivariateCornerExponent, Finsupp.degree_eq_sum, Finsupp.sum_fintype,
      Fin.sum_univ_two, two_mul] using hle
  obtain ⟨c, R, hc, hform, hR⟩ :=
    exists_bivariate_corner_normal_form Qc p hp hbound htotal
      (by simpa only [isotropicFaceExponent] using hrow)
      (by simpa only [isotropicFaceExponent] using hcolumn)
  refine ⟨c, R, hc, ?_, hR⟩
  simpa only [Qc, Q] using hform


theorem IsMaximallyCircular.exists_centered_isotropic_corner_normal_form
    {G : PlanePoly} {p : ℕ} (hmax : IsMaximallyCircular G) (hG : G ≠ 0)
    (hdegree : G.totalDegree = 2 * p) (hp : 0 < p)
    (hroots : (circularITangentPolynomial G).roots.toFinset.card = 1) :
    ∃ ξ c : ℂ, ∃ R : BidegreePolynomial ℂ,
      c ≠ 0 ∧
        isotropicTranslationEquiv ξ
            (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
          MvPolynomial.monomial (bivariateCornerExponent p) c + R ∧
        BidegreeBound (p - 1) R := by
  have hI : circularITangentPolynomial G ≠ 0 :=
    hmax.circularITangentPolynomial_ne_zero hG
  have hIdegree : (circularITangentPolynomial G).natDegree = p :=
    hmax.circularITangentPolynomial_natDegree hG hdegree
  obtain ⟨ξ, hcenterI, hcenterJ⟩ :=
    exists_simultaneously_centered_circular_tangent_polynomials hI hIdegree hroots
  obtain ⟨c, R, hc, hform, hR⟩ :=
    hmax.centered_isotropic_corner_normal_form_of_tangent_identities
      hG hdegree hp ξ hcenterI hcenterJ
  exact ⟨ξ, c, R, hc, hform, hR⟩

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic (PlaneCurveZeroSet mem_PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound {α : Type*} (S : Set α) (B : ℕ)
    (hbound : ∀ T : Finset α, (↑T : Set α) ⊆ S → T.card ≤ B) :
    S.Finite := by
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (B + 1)
  have := hbound T hT
  omega

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve (C : IrreduciblePlanePolynomial ℝ) :
    CurveSymmetries.IsIrreducibleCurve C.polynomial.totalDegree
      (PlaneCurveZeroSet C.polynomial) :=
  ⟨C.polynomial, C.irreducible.ne_zero, le_rfl, C.irreducible, rfl⟩

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_sphere_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a : PachDeZeeuw.Algebraic.Point2) {r : ℝ} (hr : 0 ≤ r) :
    (PlaneCurveZeroSet C.polynomial ∩ Metric.sphere a r).Finite := by
  by_cases hr0 : r = 0
  · subst r
    have hsphere : (Metric.sphere a 0).Finite := by
      simpa using Set.finite_singleton a
    exact hsphere.subset Set.inter_subset_right
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  apply inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound _ (2 * C.polynomial.totalDegree)
  intro T hT
  exact finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    C.polynomial a r C.polynomial.totalDegree T hrpos le_rfl
    (fun z hz ↦ (hT hz).1) (fun z hz ↦ (hT hz).2)
    (CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
      (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve C) hnot a hrpos)

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_line_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a v : PachDeZeeuw.Algebraic.Point2) (hv : v ≠ 0) :
    (PlaneCurveZeroSet C.polynomial ∩
      PlaneCurveZeroSet (affineLinePolynomial a v)).Finite := by
  apply inline_Esgk_TwoPairDistanceRepeatedAnchors__finite_of_finset_card_bound _ C.polynomial.totalDegree
  intro T hT
  exact finite_affineLine_zeroSet_card_le_of_not_subset
    C.polynomial a C.polynomial.totalDegree T hv le_rfl
    (fun z hz ↦ (hT hz).1) (fun z hz ↦ (hT hz).2)
    (CurveSymmetries.affineLine_not_subset
      (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_isIrreducibleCurve C) hnot hv)

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchors__mem_bisector_of_dist_sq_eq {b e y : PachDeZeeuw.Algebraic.Point2}
    (h : dist y b ^ 2 = dist y e ^ 2) :
    y ∈ PlaneCurveZeroSet (affineLinePolynomial
      (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)) := by
  rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
    Fin.sum_univ_two, Fin.sum_univ_two] at h
  simp only [Real.dist_eq, sq_abs] at h
  rw [mem_PlaneCurveZeroSet, affineLinePolynomial_eval]
  simp only [perpendicularBisectorBase, perpendicularBisectorDirection,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith


theorem twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e) :
    (twoPairDistanceCommonZeroSet C a a b e).Finite := by
  have hline := inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_line_finite C hnot
    (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)
    (perpendicularBisectorDirection_ne_zero hbe)
  apply Set.Finite.of_finite_fibers Prod.snd
  · apply hline.subset
    rintro y ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, inline_Esgk_TwoPairDistanceRepeatedAnchors__mem_bisector_of_dist_sq_eq (hz.2.2.1.symm.trans hz.2.2.2)⟩
  · intro y _hy
    have hfiber := (inline_Esgk_TwoPairDistanceRepeatedAnchors__carrier_inter_sphere_finite C hnot a
      (dist_nonneg (x := y) (y := b))).prod (Set.finite_singleton y)
    apply hfiber.subset
    rintro z ⟨hz, hzy⟩
    have hzy' : z.2 = y := hzy
    refine ⟨⟨hz.1, ?_⟩, hzy'⟩
    change dist z.1 a = dist y b
    have hsq := hz.2.2.1
    rw [hzy'] at hsq
    nlinarith [dist_nonneg (x := z.1) (y := a), dist_nonneg (x := y) (y := b)]

 
theorem twoPairDistanceCommonZeroSet_finite_of_target_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a c b : PachDeZeeuw.Algebraic.Point2) (hac : a ≠ c) :
    (twoPairDistanceCommonZeroSet C a c b b).Finite := by
  have hfinite := twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated
    C hnot b a c hac
  have himage : (Prod.swap '' twoPairDistanceCommonZeroSet C a c b b).Finite := by
    apply hfinite.subset
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, hz.1, hz.2.2.1.symm, hz.2.2.2.symm⟩
  exact himage.of_finite_image (Equiv.prodComm PachDeZeeuw.Algebraic.Point2 PachDeZeeuw.Algebraic.Point2).injective.injOn

 


end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic


private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one (c : ℂ) :
    MvPolynomial.monomial (bivariateCornerExponent 1) c =
      MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [MvPolynomial.monomial_eq]
  simp [bivariateCornerExponent, Finsupp.prod_fintype, Fin.prod_univ_two]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C (R : BidegreePolynomial ℂ)
    (hR : BidegreeBound 0 R) :
    R = MvPolynomial.C (R.coeff 0) := by
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  have hdegree := totalDegree_le_two_mul_of_bidegreeBound 0 hR
  omega

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw (ξ : ℂ) :
    planeIsotropicCoordinateEquiv.symm
        ((isotropicTranslationEquiv ξ).symm
          (MvPolynomial.X 0 * MvPolynomial.X 1)) =
      realToComplexPlanePolynomial
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) := by
  rcases ξ with ⟨a, b⟩
  simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply,
    inverseIsotropicTranslation, isotropicToPlaneCoordinates, planeSquaredDistancePolynomial,
    realToComplexPlanePolynomial, bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter]
  have hmk : ({ re := a, im := b } : ℂ) = (a : ℂ) + b * Complex.I := by
    apply Complex.ext <;> simp
  have hstar : (starRingEnd ℂ) ({ re := a, im := b } : ℂ) =
      (a : ℂ) - b * Complex.I := by
    apply Complex.ext <;> simp
  rw [hstar, hmk]
  simp only [map_add, map_sub, map_mul]
  ring_nf
  rw [show (MvPolynomial.C Complex.I : ComplexPlanePoly) ^ 2 = -1 by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]]
  ring

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c : ℂ} {R : BidegreePolynomial ℂ}
    (hform :
      isotropicTranslationEquiv ξ
          (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)) =
        MvPolynomial.monomial (bivariateCornerExponent 1) c + R)
    (hR : BidegreeBound 0 R) :
    realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
  have hRconst : R = MvPolynomial.C (R.coeff 0) :=
    inline_Esgk_MaximallyCircularDegreeTwoCircle__bidegreeBound_zero_eq_C R hR
  calc
    realToComplexPlanePolynomial G =
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (isotropicTranslationEquiv ξ
              (planeIsotropicCoordinateEquiv (realToComplexPlanePolynomial G)))) := by
                rw [RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.monomial (bivariateCornerExponent 1) c + R)) := by rw [hform]
    _ = planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm
            (MvPolynomial.C c * (MvPolynomial.X 0 * MvPolynomial.X 1) +
              MvPolynomial.C (R.coeff 0))) := by
            nth_rewrite 1 [hRconst]
            congr 3
            exact inline_Esgk_MaximallyCircularDegreeTwoCircle__bivariateCornerMonomial_one c
    _ = planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C c)) *
          planeIsotropicCoordinateEquiv.symm
            ((isotropicTranslationEquiv ξ).symm
              (MvPolynomial.X 0 * MvPolynomial.X 1)) +
        planeIsotropicCoordinateEquiv.symm
          ((isotropicTranslationEquiv ξ).symm (MvPolynomial.C (R.coeff 0))) := by
            rw [map_add, map_add, map_mul, map_mul]
    _ = MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C (R.coeff 0) := by
          rw [inline_Esgk_MaximallyCircularDegreeTwoCircle__isotropicTranslationCenter_zw]
          simp [planeIsotropicCoordinateEquiv_symm_apply, isotropicTranslationEquiv_symm_apply]

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq
    {G : PachDeZeeuw.Algebraic.PlanePoly} {ξ c d : ℂ}
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d) :
    Complex.ofReal (G.coeff (Finsupp.single 0 2)) = c := by
  have hdistcoeff :
      (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)).coeff
          (Finsupp.single (0 : Fin 2) 2) = 1 := by
    have htop := congrArg
      (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2))
      (homogeneousComponent_two_planeSquaredDistancePolynomial
        (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ))
    rw [MvPolynomial.coeff_homogeneousComponent] at htop
    have hsingle : Finsupp.single (1 : Fin 2) 2 ≠ Finsupp.single 0 2 := by
      intro h
      have hzero := DFunLike.congr_fun h 0
      simp at hzero
    simpa [planeRadialQuadratic, MvPolynomial.coeff_add,
      MvPolynomial.coeff_X_pow, hsingle] using htop
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)) hmap
  change MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.map Complex.ofRealHom G) =
    MvPolynomial.coeff (Finsupp.single (0 : Fin 2) 2)
      (MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
        (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
          MvPolynomial.C d) at hcoeff
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_map, hdistcoeff, MvPolynomial.coeff_C] at hcoeff
  have he : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 2 := by
    intro h
    have hzero := DFunLike.congr_fun h 0
    simp at hzero
  simpa [he] using hcoeff

private theorem inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map
    {G : PlanePoly} {ξ c d : ℂ} (hc : c ≠ 0)
    (hmap : realToComplexPlanePolynomial G =
      MvPolynomial.C c * realToComplexPlanePolynomial
          (planeSquaredDistancePolynomial (bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ)) +
        MvPolynomial.C d)
    {x : _root_.Point2} (hx : x ∈ PlaneCurveZeroSet G) :
    IsCircleFactor G := by
  let center : _root_.Point2 := bundle_Esgk_MaximallyCircularDegreeTwoCircle_isotropicTranslationCenter ξ
  let scalar : ℝ := G.coeff (Finsupp.single 0 2)
  have hcReal : Complex.ofReal scalar = c := by
    simpa only [scalar] using inline_Esgk_MaximallyCircularDegreeTwoCircle__centered_map_scalar_eq hmap
  have hxzero : MvPolynomial.eval (fun i : Fin 2 ↦ x i) G = 0 :=
    mem_PlaneCurveZeroSet.mp hx
  have hevalComplexification (F : PlanePoly) :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial F) =
        Complex.ofReal (MvPolynomial.eval (fun i : Fin 2 ↦ x i) F) := by
    have hfun : (fun i : Fin 2 ↦ Complex.ofReal (x i)) =
        (Complex.ofRealHom ∘ fun i : Fin 2 ↦ x i) := by
      rfl
    rw [realToComplexPlanePolynomial, MvPolynomial.eval_map, hfun,
      ← MvPolynomial.eval_map]
    exact (MvPolynomial.map_eval Complex.ofRealHom (fun i : Fin 2 ↦ x i) F).symm
  have heval := congrArg
    (MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))) hmap
  have hleft :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial G) = 0 := by
    simpa [hxzero] using hevalComplexification G
  have hdistEval :
      MvPolynomial.eval (fun i : Fin 2 ↦ Complex.ofReal (x i))
          (realToComplexPlanePolynomial (planeSquaredDistancePolynomial center)) =
        Complex.ofReal (dist x center ^ 2) := by
    rw [hevalComplexification, eval_planeSquaredDistancePolynomial]
  have heval' :
      0 = c * Complex.ofReal (dist x center ^ 2) + d := by
    simpa only [center, hleft, map_add, map_mul, MvPolynomial.eval_C,
      hdistEval] using heval
  have hd : d = -c * Complex.ofReal (dist x center ^ 2) := by
    calc
      d = (c * Complex.ofReal (dist x center ^ 2) + d) -
          c * Complex.ofReal (dist x center ^ 2) := by ring
      _ = 0 - c * Complex.ofReal (dist x center ^ 2) := by rw [← heval']
      _ = -c * Complex.ofReal (dist x center ^ 2) := by ring
  have hscalar : scalar ≠ 0 := by
    intro hzero
    apply hc
    simpa [hzero] using hcReal.symm
  have hreal :
      G = MvPolynomial.C scalar * circleEquationPolynomial center (dist x center) := by
    apply MvPolynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
    change MvPolynomial.map Complex.ofRealHom G = MvPolynomial.map Complex.ofRealHom
      (MvPolynomial.C scalar * circleEquationPolynomial center (dist x center))
    rw [map_mul, MvPolynomial.map_C, circleEquationPolynomial, map_sub,
      MvPolynomial.map_C]
    have hmap' : MvPolynomial.map Complex.ofRealHom G =
        MvPolynomial.C c * MvPolynomial.map Complex.ofRealHom
            (planeSquaredDistancePolynomial center) + MvPolynomial.C d := by
      simpa only [realToComplexPlanePolynomial, center] using hmap
    have hcReal' : Complex.ofRealHom scalar = c := hcReal
    rw [hmap', hcReal', hd]
    simp only [map_neg, map_mul]
    have hofRealHom_apply (t : ℝ) : Complex.ofRealHom t = (t : ℂ) := rfl
    rw [hofRealHom_apply]
    rw [Complex.ofReal_pow]
    ring
  refine ⟨center, dist x center, dist_nonneg, ?_⟩
  rw [hreal]
  exact associated_unit_mul_left _ _
    ((isUnit_iff_ne_zero.mpr hscalar).map (MvPolynomial.C : ℝ →+* PlanePoly))

 
theorem isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
    {H : PlanePoly} (hH : H ≠ 0) (hmax : IsMaximallyCircular H)
    (hdegree : H.totalDegree = 2) {x : _root_.Point2}
    (hx : x ∈ PlaneCurveZeroSet H) :
    IsCircleFactor H := by
  have hdegreeOne : H.totalDegree = 2 * 1 := by omega
  have hqdegree : (circularITangentPolynomial H).natDegree = 1 :=
    hmax.circularITangentPolynomial_natDegree hH hdegreeOne
  have hrootpos : 0 < (circularITangentPolynomial H).roots.toFinset.card := by
    apply Polynomial.roots_toFinset_card_pos_of_natDegree_pos
    rw [hqdegree]
    omega
  have hrootle : (circularITangentPolynomial H).roots.toFinset.card ≤ 1 := by
    calc
      (circularITangentPolynomial H).roots.toFinset.card ≤
          (circularITangentPolynomial H).roots.card :=
        (circularITangentPolynomial H).roots.toFinset_card_le
      _ = (circularITangentPolynomial H).natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      _ = 1 := hqdegree
  have hrootcard : (circularITangentPolynomial H).roots.toFinset.card = 1 := by omega
  obtain ⟨ξ, c, R, hc, hform, hR⟩ :=
    hmax.exists_centered_isotropic_corner_normal_form hH hdegreeOne (by omega) hrootcard
  exact inline_Esgk_MaximallyCircularDegreeTwoCircle__isCircleFactor_of_centered_map hc
    (inline_Esgk_MaximallyCircularDegreeTwoCircle__realToComplex_eq_centered_corner_one hform hR) hx

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open PachDeZeeuw.Algebraic (PlaneCurveZeroSet mem_PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_carrier_isIrreducibleCurve
    (C : IrreduciblePlanePolynomial ℝ) :
    CurveSymmetries.IsIrreducibleCurve C.polynomial.totalDegree
      (PlaneCurveZeroSet C.polynomial) :=
  ⟨C.polynomial, C.irreducible.ne_zero, le_rfl, C.irreducible, rfl⟩

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_carrier_degree_pos
    (C : IrreduciblePlanePolynomial ℝ) :
    0 < C.polynomial.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  apply C.irreducible.not_isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨C.polynomial.coeff 0, ?_,
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree⟩
  rw [isUnit_iff_ne_zero]
  intro hcoeff
  apply C.irreducible.ne_zero
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree, hcoeff, map_zero]

private theorem inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_source_fiber_card_le
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet C.polynomial))
    (a b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e)
    (hU : (twoPairDistanceCommonZeroSet C a a b e).Finite)
    (U : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2))
    (hUsub : (U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2)) ⊆
      twoPairDistanceCommonZeroSet C a a b e)
    (y : PachDeZeeuw.Algebraic.Point2) :
    (U.filter (fun z ↦ z.2 = y)).card ≤ 2 * C.polynomial.totalDegree := by
  classical
  let fiber : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) := U.filter (fun z ↦ z.2 = y)
  let firstFiber : Finset PachDeZeeuw.Algebraic.Point2 := fiber.image Prod.fst
  have hfirstCard : fiber.card = firstFiber.card := by
    symm
    apply Finset.card_image_iff.mpr
    intro z hz w hw hzw
    apply Prod.ext hzw
    exact (Finset.mem_filter.mp hz).2.trans
      (Finset.mem_filter.mp hw).2.symm
  have hfirstZero : ∀ z ∈ firstFiber,
      MvPolynomial.eval (fun i ↦ z i) C.polynomial = 0 := by
    intro z hz
    obtain ⟨zw, hzw, rfl⟩ := Finset.mem_image.mp hz
    have hzwU := hUsub (Finset.mem_filter.mp hzw).1
    rw [← mem_PlaneCurveZeroSet]
    exact hzwU.1
  have hfirstSphere : ∀ z ∈ firstFiber,
      z ∈ Metric.sphere a (dist y b) := by
    intro z hz
    obtain ⟨zw, hzw, rfl⟩ := Finset.mem_image.mp hz
    have hzwU := hUsub (Finset.mem_filter.mp hzw).1
    have hsecond : zw.2 = y := (Finset.mem_filter.mp hzw).2
    have hsq := hzwU.2.2.1
    rw [hsecond] at hsq
    change dist zw.1 a = dist y b
    nlinarith [hsq, dist_nonneg (x := zw.1) (y := a),
      dist_nonneg (x := y) (y := b)]
  by_cases hr0 : dist y b = 0
  · have hfirstSingleton : (firstFiber : Set PachDeZeeuw.Algebraic.Point2) ⊆ ({a} : Set PachDeZeeuw.Algebraic.Point2) := by
      intro z hz
      change z ∈ firstFiber at hz
      obtain ⟨zw, hzw, rfl⟩ := Finset.mem_image.mp hz
      have hzwU := hUsub (Finset.mem_filter.mp hzw).1
      have hsecond : zw.2 = y := (Finset.mem_filter.mp hzw).2
      have hsq := hzwU.2.2.1
      rw [hsecond, hr0] at hsq
      have hzero : dist zw.1 a = 0 := by
        nlinarith [hsq, dist_nonneg (x := zw.1) (y := a)]
      exact Set.mem_singleton_iff.mpr (dist_eq_zero.mp hzero)
    calc
      fiber.card = firstFiber.card := hfirstCard
      _ ≤ ({a} : Finset PachDeZeeuw.Algebraic.Point2).card := Finset.card_le_card (by
        intro z hz
        exact Finset.mem_singleton.mpr (hfirstSingleton hz))
      _ = 1 := by simp
      _ ≤ 2 * C.polynomial.totalDegree := by
        have hdegree := inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_carrier_degree_pos C
        omega
  · have hrpos : 0 < dist y b := lt_of_le_of_ne
      (dist_nonneg (x := y) (y := b)) (Ne.symm hr0)
    have hnotSphere : ¬ Metric.sphere a (dist y b) ⊆
        PlaneCurveZeroSet C.polynomial :=
      CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
        (inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_carrier_isIrreducibleCurve C) hnot a hrpos
    have hfirstBound := finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
      C.polynomial a (dist y b) C.polynomial.totalDegree firstFiber hrpos
      le_rfl hfirstZero hfirstSphere hnotSphere
    calc
      fiber.card = firstFiber.card := hfirstCard
      _ ≤ 2 * C.polynomial.totalDegree := hfirstBound

theorem twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_source_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet C.polynomial))
    (a b e : PachDeZeeuw.Algebraic.Point2) (hbe : b ≠ e) :
    (twoPairDistanceCommonZeroSet C a a b e).ncard ≤
      2 * C.polynomial.totalDegree ^ 2 := by
  classical
  let U := twoPairDistanceCommonZeroSet C a a b e
  have hU : U.Finite := by
    simpa [U] using
      twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated C hnot a b e hbe
  let Ufin : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) := hU.toFinset
  let T : Finset PachDeZeeuw.Algebraic.Point2 := Ufin.image Prod.snd
  have hTline : (T : Set PachDeZeeuw.Algebraic.Point2) ⊆
      PlaneCurveZeroSet (affineLinePolynomial
        (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)) := by
    intro y hy
    change y ∈ T at hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hzU := hU.mem_toFinset.mp hz
    have h := hzU.2.2.1.symm.trans hzU.2.2.2
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two] at h
    simp only [Real.dist_eq, sq_abs] at h
    rw [mem_PlaneCurveZeroSet, affineLinePolynomial_eval]
    simp only [perpendicularBisectorBase, perpendicularBisectorDirection,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith
  have hv : perpendicularBisectorDirection b e ≠ 0 :=
    perpendicularBisectorDirection_ne_zero hbe
  have hlineNot : ¬ PlaneCurveZeroSet (affineLinePolynomial
      (perpendicularBisectorBase b e) (perpendicularBisectorDirection b e)) ⊆
        PlaneCurveZeroSet C.polynomial :=
    CurveSymmetries.affineLine_not_subset
      (inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_carrier_isIrreducibleCurve C) hnot hv
  have hTcard : T.card ≤ C.polynomial.totalDegree :=
    finite_affineLine_zeroSet_card_le_of_not_subset C.polynomial
      (perpendicularBisectorBase b e) C.polynomial.totalDegree T hv le_rfl
      (by
        intro z hz
        obtain ⟨zw, hzw, rfl⟩ := Finset.mem_image.mp hz
        rw [← mem_PlaneCurveZeroSet]
        exact (hU.mem_toFinset.mp hzw).2.1)
      (fun z hz ↦ hTline hz)
      hlineNot
  let fiber : PachDeZeeuw.Algebraic.Point2 → Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    fun y ↦ Ufin.filter (fun z ↦ z.2 = y)
  have hfiber : ∀ y ∈ T, (fiber y).card ≤ 2 * C.polynomial.totalDegree := by
    intro y hy
    apply inline_Esgk_TwoPairDistanceRepeatedAnchorCardinality__repeated_source_fiber_card_le C hnot a b e hbe hU Ufin
    · intro z hz
      exact hU.mem_toFinset.mp hz
  have hcover : Ufin ⊆ T.biUnion fiber := by
    intro z hz
    exact Finset.mem_biUnion.mpr ⟨z.2,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩,
      Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  rw [Set.ncard_eq_toFinset_card _ hU]
  change Ufin.card ≤ 2 * C.polynomial.totalDegree ^ 2
  calc
    Ufin.card ≤ (T.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ y ∈ T, (fiber y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ T, 2 * C.polynomial.totalDegree := by
      exact Finset.sum_le_sum fun y hy ↦ hfiber y hy
    _ = T.card * (2 * C.polynomial.totalDegree) := by simp
    _ ≤ C.polynomial.totalDegree * (2 * C.polynomial.totalDegree) :=
      Nat.mul_le_mul_right _ hTcard
    _ = 2 * C.polynomial.totalDegree ^ 2 := by ring

theorem twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_target_anchor_repeated
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet C.polynomial))
    (a c b : PachDeZeeuw.Algebraic.Point2) (hac : a ≠ c) :
    (twoPairDistanceCommonZeroSet C a c b b).ncard ≤
      2 * C.polynomial.totalDegree ^ 2 := by
  let U := twoPairDistanceCommonZeroSet C a c b b
  let V := twoPairDistanceCommonZeroSet C b b a c
  have hU : U.Finite := by
    simpa [U] using
      twoPairDistanceCommonZeroSet_finite_of_target_anchor_repeated C hnot a c b hac
  have hV : V.Finite := by
    simpa [V] using
      twoPairDistanceCommonZeroSet_finite_of_source_anchor_repeated C hnot b a c hac
  have hswap : Prod.swap '' U ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hz.2.1, hz.1, hz.2.2.1.symm, hz.2.2.2.symm⟩
  calc
    U.ncard = (Prod.swap '' U).ncard := by
      symm
      exact Set.ncard_image_of_injective U
        (Equiv.prodComm PachDeZeeuw.Algebraic.Point2 PachDeZeeuw.Algebraic.Point2).injective
    _ ≤ V.ncard := Set.ncard_le_ncard hswap hV
    _ ≤ 2 * C.polynomial.totalDegree ^ 2 :=
      twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_source_anchor_repeated
        C hnot b a c hac

theorem twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_repeated_anchor
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet C.polynomial))
    (a c b e : PachDeZeeuw.Algebraic.Point2) (hlabels : (a, b) ≠ (c, e))
    (hrepeated : a = c ∨ b = e) :
    (twoPairDistanceCommonZeroSet C a c b e).ncard ≤
      2 * C.polynomial.totalDegree ^ 2 := by
  rcases hrepeated with hac | hbe
  · subst c
    apply twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_source_anchor_repeated
      C hnot a b e
    intro hbe'
    exact hlabels (Prod.ext rfl hbe')
  · subst e
    apply twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_target_anchor_repeated
      C hnot a c b
    intro hac'
    exact hlabels (Prod.ext hac' rfl)

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one
    (x v : PachDeZeeuw.Algebraic.Point2) :
    (affineLinePolynomial x v).totalDegree ≤ 1 := by
  have hsub0 :
      (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 0 : PlanePoly) (x 0))
  have hsub1 :
      (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree ≤ 1 := by
    simpa using
      (MvPolynomial.totalDegree_sub_C_le
        (MvPolynomial.X 1 : PlanePoly) (x 1))
  have hterm0 :
      (MvPolynomial.C (v 1) *
        (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 1) : PlanePoly).totalDegree +
          (MvPolynomial.X 0 - MvPolynomial.C (x 0) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub0
  have hterm1 :
      (MvPolynomial.C (v 0) *
        (MvPolynomial.X 1 - MvPolynomial.C (x 1)) : PlanePoly).totalDegree ≤ 1 := by
    calc
      _ ≤ (MvPolynomial.C (v 0) : PlanePoly).totalDegree +
          (MvPolynomial.X 1 - MvPolynomial.C (x 1) : PlanePoly).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 1 := by simpa using hsub1
  have hsub := MvPolynomial.totalDegree_sub
      (MvPolynomial.C (v 1) * (MvPolynomial.X 0 - MvPolynomial.C (x 0)) : PlanePoly)
      (MvPolynomial.C (v 0) * (MvPolynomial.X 1 - MvPolynomial.C (x 1)))
  simpa [affineLinePolynomial] using hsub.trans (max_le hterm0 hterm1)

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite
    {x v : PachDeZeeuw.Algebraic.Point2} (hv : v ≠ 0) :
    (PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
  let f : ℝ → PachDeZeeuw.Algebraic.Point2 := fun t ↦ x + t • v
  have hf : Function.Injective f := by
    intro s t hst
    by_cases hv0 : v 0 = 0
    · have hv1 : v 1 ≠ 0 := by
        intro hv1
        apply hv
        ext i
        fin_cases i <;> assumption
      have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hst
      change x 1 + s * v 1 = x 1 + t * v 1 at hcoord
      have hst' : (s - t) * v 1 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv1'
      · linarith
      · exact (hv1 hv1').elim
    · have hcoord := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hst
      change x 0 + s * v 0 = x 0 + t * v 0 at hcoord
      have hst' : (s - t) * v 0 = 0 := by linarith
      rcases mul_eq_zero.mp hst' with hst' | hv0'
      · linarith
      · exact (hv0 hv0').elim
  have hmem : ∀ t : ℝ, f t ∈ PlaneCurveZeroSet (affineLinePolynomial x v) := by
    intro t
    change MvPolynomial.eval (fun i ↦ (f t) i)
      (affineLinePolynomial x v) = 0
    rw [affineLinePolynomial_eval]
    change v 1 * (x 0 + t * v 0 - x 0) -
      v 0 * (x 1 + t * v 1 - x 1) = 0
    ring
  refine (Set.infinite_range_of_injective hf).mono ?_
  rintro z ⟨t, rfl⟩
  exact hmem t

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet
    {a b c : ℝ} (hab : (a, b) ≠ (0, 0)) :
    ∃ x v : PachDeZeeuw.Algebraic.Point2, v ≠ 0 ∧
      {p : PachDeZeeuw.Algebraic.Point2 | a * p 0 + b * p 1 = c} =
        PlaneCurveZeroSet (affineLinePolynomial x v) := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      exact hab (by simp [ha, hb])
    let x : PachDeZeeuw.Algebraic.Point2 := !₂[0, c / b]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, 0]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact hb (by simpa using h0)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp [x, v, ha, hb, sub_eq_zero, eq_div_iff hb, mul_comm]
  · let x : PachDeZeeuw.Algebraic.Point2 := !₂[c / a, 0]
    let v : PachDeZeeuw.Algebraic.Point2 := !₂[-b, a]
    refine ⟨x, v, ?_, ?_⟩
    · intro hv
      have h0 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 0) hv
      have h1 := congrArg (fun z : PachDeZeeuw.Algebraic.Point2 ↦ z 1) hv
      simp [v] at h0 h1
      exact ha (by simpa using h1)
    · rw [affineLinePolynomial_zeroSet_eq_line]
      ext p
      simp only [Set.mem_ofPred_eq]
      simp [x, v]
      constructor <;> intro h
      · field_simp [ha] at h ⊢
        linarith
      · field_simp [ha] at h ⊢
        linarith

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos
    {G : PlanePoly} (hG : Irreducible G) : 0 < G.totalDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  apply hG.not_isUnit
  rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced]
  refine ⟨G.coeff 0, ?_, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree⟩
  rw [isUnit_iff_ne_zero]
  intro hcoeff
  apply hG.ne_zero
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegree, hcoeff, map_zero]

theorem IsMaximallyCircular.two_le_totalDegree_of_irreducible
    {G : PlanePoly} (hmax : IsMaximallyCircular G)
    (hG : Irreducible G) : 2 ≤ G.totalDegree := by
  have hpos := inline_Esgk_MaximallyCircularRealCarrierNondegenerate__irreducible_totalDegree_pos hG
  have heven := hmax.1
  omega

private theorem inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd
    {G q : PlanePoly} (hG : G ∣ q) (hq : q ≠ 0) :
    G.totalDegree ≤ q.totalDegree :=
  MvPolynomial.totalDegree_le_of_dvd_of_isDomain hG hq


theorem maximallyCircular_realCarrier_not_isLineOrCircle
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    {a b : PachDeZeeuw.Algebraic.Point2} (ha : a ∈ PlaneCurveZeroSet G)
    (hb : b ∈ PlaneCurveZeroSet G) (hab : a ≠ b) :
    ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G) := by
  intro hcontrolled
  have hGdegree : 2 ≤ G.totalDegree :=
    hmax.two_le_totalDegree_of_irreducible hGirreducible
  rcases hcontrolled with hline | hcircle
  · rcases hline with ⟨α, β, γ, habcoeff, hcarrier⟩
    obtain ⟨x, v, hv, hlinezero⟩ :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__line_set_eq_affineLinePolynomial_zeroSet habcoeff
    have hcarrier' : PlaneCurveZeroSet G =
        PlaneCurveZeroSet (affineLinePolynomial x v) :=
      hcarrier.trans hlinezero
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (affineLinePolynomial x v)).Infinite := by
      rw [hcarrier']
      simpa using inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_zeroSet_infinite hv
    have hdiv : G ∣ affineLinePolynomial x v :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero : affineLinePolynomial x v ≠ 0 :=
      (affineLinePolynomial_irreducible hv).ne_zero
    have hGle : G.totalDegree ≤
        (affineLinePolynomial x v).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero
    have hqle : (affineLinePolynomial x v).totalDegree ≤ 1 :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__affineLinePolynomial_totalDegree_le_one x v
    have hGleOne : G.totalDegree ≤ 1 := hGle.trans hqle
    omega
  · rcases hcircle with ⟨center, r, hcarrier⟩
    have haSphere : a ∈ Metric.sphere center r := hcarrier ▸ ha
    have hbSphere : b ∈ Metric.sphere center r := hcarrier ▸ hb
    have hrnonneg : 0 ≤ r := by
      have hdist := Metric.mem_sphere.mp haSphere
      linarith [dist_nonneg (x := a) (y := center)]
    have hr : 0 < r := by
      rcases lt_or_eq_of_le hrnonneg with hr | rfl
      · exact hr
      · have haa : a = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp haSphere)
        have hbb : b = center := by
          apply dist_eq_zero.mp
          simpa using (Metric.mem_sphere.mp hbSphere)
        exact False.elim (hab (haa.trans hbb.symm))
    have hqzero :
        PlaneCurveZeroSet (circleEquationPolynomial center r) = Metric.sphere center r :=
      circleEquationPolynomial_zeroSet center hr.le
    have hinf :
        (PlaneCurveZeroSet G ∩
          PlaneCurveZeroSet (circleEquationPolynomial center r)).Infinite := by
      rw [hcarrier, hqzero]
      simpa using sphere_infinite center hr
    have hdiv : G ∣ circleEquationPolynomial center r :=
      dvd_of_infinite_irreducible_zeroSet_intersection hGirreducible hinf
    have hqzero' : circleEquationPolynomial center r ≠ 0 :=
      circleEquationPolynomial_ne_zero center (ne_of_gt hr)
    have hGle : G.totalDegree ≤
        (circleEquationPolynomial center r).totalDegree :=
      inline_Esgk_MaximallyCircularRealCarrierNondegenerate__totalDegree_le_of_dvd hdiv hqzero'
    have hqdegree : (circleEquationPolynomial center r).totalDegree = 2 :=
      circleEquationPolynomial_totalDegree_eq center r
    have hGdegree_le_two : G.totalDegree ≤ 2 := by
      rw [hqdegree] at hGle
      exact hGle
    have hGdegree_eq_two : G.totalDegree = 2 := by
      have heven : 2 * planeCircularLocalOrderI G = G.totalDegree := hmax.1
      omega
    exact hnotCircle
      (isCircleFactor_of_maximallyCircular_degree_two_of_real_zero
        hGirreducible.ne_zero hmax hGdegree_eq_two ha)

end Esgk

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open MvPolynomial
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

private theorem inline_Esgk_TwoPairDistanceCardinality__plane_totalDegree_aeval_le {R : Type*} [CommSemiring R]
    {σ τ : Type*} (f : σ → MvPolynomial τ R)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  have hsum : MvPolynomial.aeval f p =
      ∑ v ∈ p.support,
        MvPolynomial.aeval f (MvPolynomial.monomial v (MvPolynomial.coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro v hv
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc
    ∑ i ∈ v.support, (f i ^ v i).totalDegree
        ≤ ∑ i ∈ v.support, v i * (f i).totalDegree :=
      Finset.sum_le_sum (fun i _ ↦ MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ i ∈ v.support, v i * 1 :=
      Finset.sum_le_sum (fun i _ ↦ Nat.mul_le_mul (le_refl (v i)) (hf i))
    _ = v.sum (fun _ e ↦ e) := by simp only [mul_one]; rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv

private theorem inline_Esgk_TwoPairDistanceCardinality__planeAffineCoordinatePolynomial_totalDegree_le
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (i : Fin 2) :
    (planeAffineCoordinatePolynomial g i).totalDegree ≤ 1 := by
  unfold planeAffineCoordinatePolynomial
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact LinearMap.toMvPolynomial_totalDegree_le _ _ _ _
  · simp

private theorem inline_Esgk_TwoPairDistanceCardinality__planeAffinePolynomialEquiv_totalDegree_le
    (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) (p : PlanePoly) :
    (planeAffinePolynomialEquiv g p).totalDegree ≤ p.totalDegree := by
  change (MvPolynomial.bind₁ (planeAffineCoordinatePolynomial g) p).totalDegree ≤
    p.totalDegree
  rw [← MvPolynomial.aeval_eq_bind₁]
  exact inline_Esgk_TwoPairDistanceCardinality__plane_totalDegree_aeval_le (planeAffineCoordinatePolynomial g)
    (inline_Esgk_TwoPairDistanceCardinality__planeAffineCoordinatePolynomial_totalDegree_le g) p

private theorem inline_Esgk_TwoPairDistanceCardinality__affineIsometryTransport_totalDegree_le
    (C : IrreduciblePlanePolynomial ℝ) (g : PachDeZeeuw.Algebraic.Point2 ≃ᵃⁱ[ℝ] PachDeZeeuw.Algebraic.Point2) :
    (C.affineIsometryTransport g).polynomial.totalDegree ≤ C.polynomial.totalDegree := by
  rw [C.affineIsometryTransport_polynomial]
  exact inline_Esgk_TwoPairDistanceCardinality__planeAffinePolynomialEquiv_totalDegree_le g.symm C.polynomial


theorem twoPairDistanceCommonZeroSet_ncard_le_of_finite_distinct_endpoints
    (C : IrreduciblePlanePolynomial ℝ) (a c b e : PachDeZeeuw.Algebraic.Point2)
    (hac : a ≠ c) (hbe : b ≠ e) (d : ℕ) (hd : 2 ≤ d)
    (hCdegree : C.polynomial.totalDegree ≤ d)
    (hfinite : (twoPairDistanceCommonZeroSet C a c b e).Finite) :
    (twoPairDistanceCommonZeroSet C a c b e).ncard ≤ 80 * d ^ 2 := by
  obtain ⟨g₁, r₁, hr₁, hg₁a, hg₁c, _, _⟩ :=
    C.exists_affineIsometryTransport_normalizedDistancePair hac
  obtain ⟨g₂, r₂, hr₂, hg₂b, hg₂e, _, _⟩ :=
    C.exists_affineIsometryTransport_normalizedDistancePair hbe
  have hdeg₁ :
      (C.affineIsometryTransport g₁).polynomial.totalDegree ≤ d :=
    (inline_Esgk_TwoPairDistanceCardinality__affineIsometryTransport_totalDegree_le C g₁).trans hCdegree
  have hdeg₂ :
      (C.affineIsometryTransport g₂).polynomial.totalDegree ≤ d :=
    (inline_Esgk_TwoPairDistanceCardinality__affineIsometryTransport_totalDegree_le C g₂).trans hCdegree
  have hnormfin := normalizedDistancePairCommonZeroSet_finite_of_twoPair_finite
    C g₁ g₂ a c b e hg₁a hg₁c hg₂b hg₂e hfinite
  have hnormcard := normalizedDistancePairCommonZeroSet_ncard_eq_twoPairDistanceCommonZeroSet_ncard
    C g₁ g₂ a c b e hg₁a hg₁c hg₂b hg₂e hfinite
  have hnormbound := normalizedDistancePairCommonZeroSet_ncard_le
    (C.affineIsometryTransport g₁) (C.affineIsometryTransport g₂) r₁ r₂
    hr₂.ne' d hd hdeg₁ hdeg₂ hnormfin
  calc
    (twoPairDistanceCommonZeroSet C a c b e).ncard =
        (normalizedDistancePairCommonZeroSet
          (C.affineIsometryTransport g₁)
          (C.affineIsometryTransport g₂) r₁ r₂).ncard := hnormcard.symm
    _ ≤ 80 * d ^ 2 := hnormbound


theorem twoPairDistanceCommonZeroSet_ncard_le_of_finite
    (C : IrreduciblePlanePolynomial ℝ)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet C.polynomial))
    (a c b e : PachDeZeeuw.Algebraic.Point2) (hlabels : (a, b) ≠ (c, e))
    (d : ℕ) (hd : 2 ≤ d) (hCdegree : C.polynomial.totalDegree ≤ d)
    (hfinite : (twoPairDistanceCommonZeroSet C a c b e).Finite) :
    (twoPairDistanceCommonZeroSet C a c b e).ncard ≤ 80 * d ^ 2 := by
  by_cases hrepeated : a = c ∨ b = e
  · calc
      _ ≤ 2 * C.polynomial.totalDegree ^ 2 :=
        twoPairDistanceCommonZeroSet_ncard_le_two_mul_degree_sq_of_repeated_anchor
          C hnot a c b e hlabels hrepeated
      _ ≤ 2 * d ^ 2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hCdegree 2)
      _ ≤ 80 * d ^ 2 := Nat.mul_le_mul_right _ (by omega)
  · exact twoPairDistanceCommonZeroSet_ncard_le_of_finite_distinct_endpoints
      C a c b e (fun h ↦ hrepeated (Or.inl h)) (fun h ↦ hrepeated (Or.inr h))
      d hd hCdegree hfinite

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput Point4 auxCurve auxPointSet)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet mem_PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


private theorem inline_Esgk_AuxiliaryIncidenceCodegree__auxCurve_encodedPair_distance
    {d : ℕ} (X : PreparedBipartiteInput d)
    (ij : X.P₁ × X.P₁) (pq : X.P₂ × X.P₂)
    (hmem : encodedAuxPoint
        ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈ auxCurve X ij.1 ij.2) :
    dist (ij.1 : PachDeZeeuw.Algebraic.Point2) (pq.1 : PachDeZeeuw.Algebraic.Point2) ^ 2 =
      dist (ij.2 : PachDeZeeuw.Algebraic.Point2) (pq.2 : PachDeZeeuw.Algebraic.Point2) ^ 2 := by
  have hsq := hmem.2.2
  change dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxFirst (encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 =
    dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxSecond (encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 at hsq
  simpa using hsq


theorem auxPointPair_twoCurveLabels_card_le
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d)
    (pq rs : X.P₂ × X.P₂) (hlabels : pq ≠ rs)
    (hfinite :
      (twoPairDistanceCommonZeroSet (preparedSecondCurveIrreducible X)
        (pq.1 : PachDeZeeuw.Algebraic.Point2) (rs.1 : PachDeZeeuw.Algebraic.Point2)
        (pq.2 : PachDeZeeuw.Algebraic.Point2) (rs.2 : PachDeZeeuw.Algebraic.Point2)).Finite) :
    ((Finset.univ : Finset (X.P₁ × X.P₁)).filter (fun ij ↦
      encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2 ∧
      encodedAuxPoint ((rs.1 : PachDeZeeuw.Algebraic.Point2), (rs.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2)).card ≤ 80 * d ^ 2 := by
  let U : Set (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    twoPairDistanceCommonZeroSet (preparedSecondCurveIrreducible X)
      (pq.1 : PachDeZeeuw.Algebraic.Point2) (rs.1 : PachDeZeeuw.Algebraic.Point2) (pq.2 : PachDeZeeuw.Algebraic.Point2) (rs.2 : PachDeZeeuw.Algebraic.Point2)
  have hnot : ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial) := by
    change ¬ CurveSymmetries.IsLineOrCircle
      (PlaneCurveZeroSet (preparedSecondCurvePolynomial X))
    rw [← preparedSecondCurvePolynomial_zeroSet X]
    exact selfCurvePreparedInput_not_isLineOrCircle hself
  have hUcard : U.ncard ≤ 80 * d ^ 2 := by
    apply twoPairDistanceCommonZeroSet_ncard_le_of_finite
      (preparedSecondCurveIrreducible X) hnot
      (pq.1 : PachDeZeeuw.Algebraic.Point2) (rs.1 : PachDeZeeuw.Algebraic.Point2)
      (pq.2 : PachDeZeeuw.Algebraic.Point2) (rs.2 : PachDeZeeuw.Algebraic.Point2) ?_ d hd
      (preparedSecondCurvePolynomial_totalDegree_le X) hfinite
    intro heq
    apply hlabels
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · apply Subtype.ext
      exact congrArg Prod.snd heq
  let F : Finset (X.P₁ × X.P₁) := (Finset.univ : Finset (X.P₁ × X.P₁)).filter
    (fun ij ↦
      encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2 ∧
      encodedAuxPoint ((rs.1 : PachDeZeeuw.Algebraic.Point2), (rs.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2)
  have hlabel_mem_curve (ij : {ij // ij ∈ F}) :
      ((ij.1.1 : PachDeZeeuw.Algebraic.Point2), (ij.1.2 : PachDeZeeuw.Algebraic.Point2)) ∈ U := by
    have hiC : (ij.1.1 : PachDeZeeuw.Algebraic.Point2) ∈
        PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial := by
      rw [preparedSecondCurveIrreducible_polynomial]
      rw [← preparedSecondCurvePolynomial_zeroSet X]
      rw [← hself]
      exact X.hP₁ ij.1.1.property
    have hjC : (ij.1.2 : PachDeZeeuw.Algebraic.Point2) ∈
        PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial := by
      rw [preparedSecondCurveIrreducible_polynomial]
      rw [← preparedSecondCurvePolynomial_zeroSet X]
      rw [← hself]
      exact X.hP₁ ij.1.2.property
    have hmem := Finset.mem_filter.mp ij.property
    refine ⟨hiC, hjC, ?_, ?_⟩
    · exact inline_Esgk_AuxiliaryIncidenceCodegree__auxCurve_encodedPair_distance X ij.1 pq hmem.2.1
    · exact inline_Esgk_AuxiliaryIncidenceCodegree__auxCurve_encodedPair_distance X ij.1 rs hmem.2.2
  let f : {ij // ij ∈ F} → U := fun ij =>
    ⟨((ij.1.1 : PachDeZeeuw.Algebraic.Point2), (ij.1.2 : PachDeZeeuw.Algebraic.Point2)), hlabel_mem_curve ij⟩
  have hf : Function.Injective f := by
    intro ij kl h
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (congrArg Subtype.val h)
    · apply Subtype.ext
      exact congrArg Prod.snd (congrArg Subtype.val h)
  letI : Fintype U := hfinite.fintype
  have hcard : Fintype.card {ij // ij ∈ F} ≤ Fintype.card U :=
    Fintype.card_le_of_injective f hf
  calc
    ((Finset.univ : Finset (X.P₁ × X.P₁)).filter (fun ij ↦
      encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2 ∧
      encodedAuxPoint ((rs.1 : PachDeZeeuw.Algebraic.Point2), (rs.2 : PachDeZeeuw.Algebraic.Point2)) ∈
          auxCurve X ij.1 ij.2)).card = F.card := by rfl
    _ = Fintype.card {ij // ij ∈ F} := by simp
    _ ≤ Fintype.card U := hcard
    _ = U.ncard := Set.fintypeCard_eq_ncard U
    _ ≤ 80 * d ^ 2 := hUcard

end Esgk
end

end





section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

private theorem inline_Esgk_PlaneCurveRadialNondivisibility__eval_mkPoint2_eq_evalPlane (G : PlanePoly) (z : ℝ × ℝ) :
    MvPolynomial.eval (fun i ↦ mkPoint2 z.1 z.2 i) G = evalPlane G z := by
  unfold evalPlane
  apply congrArg (fun f ↦ MvPolynomial.eval f G)
  funext i
  fin_cases i <;> simp [mkPoint2]

private theorem inline_Esgk_PlaneCurveRadialNondivisibility__evalPlane_eq_zero_of_dvd {G H : PlanePoly} (hdiv : G ∣ H)
    {z : ℝ × ℝ} (hz : evalPlane G z = 0) : evalPlane H z = 0 := by
  obtain ⟨J, hJ⟩ := hdiv
  rw [hJ]
  simp only [evalPlane, map_mul]
  change evalPlane G z * evalPlane J z = 0
  rw [hz, zero_mul]

private theorem inline_Esgk_PlaneCurveRadialNondivisibility__planeCurve_inter_sphere_finite {G : PlanePoly} (hG : Irreducible G)
    (hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G))
    (a : PachDeZeeuw.Algebraic.Point2) {r : ℝ} (hr : 0 ≤ r) :
    (PlaneCurveZeroSet G ∩ Metric.sphere a r).Finite := by
  classical
  by_cases hr0 : r = 0
  · subst r
    have hsphere : (Metric.sphere a 0).Finite := by
      simp
    exact hsphere.subset Set.inter_subset_right
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hcurve : CurveSymmetries.IsIrreducibleCurve G.totalDegree (PlaneCurveZeroSet G) :=
    ⟨G, hG.ne_zero, le_rfl, hG, rfl⟩
  by_contra hinf
  obtain ⟨T, hT, hcard⟩ :=
    Set.Infinite.exists_subset_card_eq hinf (2 * G.totalDegree + 1)
  have hbound := finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
    G a r G.totalDegree T hrpos le_rfl
    (fun p hp ↦ (hT hp).1) (fun p hp ↦ (hT hp).2)
    (CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
      hcurve hnot a hrpos)
  omega


private theorem inline_Esgk_PlaneCurveRadialNondivisibility__not_constant_radius_on_injective_interval {G : PlanePoly}
    (hG : Irreducible G) (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (a : PachDeZeeuw.Algebraic.Point2) (γ : ℝ → ℝ × ℝ) {t₀ ε : ℝ} (hε : 0 < ε)
    (hγ : Function.Injective γ)
    (hcurve : ∀ t ∈ Metric.ball t₀ ε, evalPlane G (γ t) = 0)
    (hconstant : ∃ c : ℝ, ∀ t ∈ Metric.ball t₀ ε, planeSquaredRadius a (γ t) = c) :
    False := by
  let p : ℝ → PachDeZeeuw.Algebraic.Point2 := fun t ↦ mkPoint2 (γ t).1 (γ t).2
  have hp : Function.Injective p := by
    intro t u htu
    apply hγ
    apply Prod.ext
    · have h₀ := congrArg (fun q : PachDeZeeuw.Algebraic.Point2 ↦ q 0) htu
      simpa [p, mkPoint2] using h₀
    · have h₁ := congrArg (fun q : PachDeZeeuw.Algebraic.Point2 ↦ q 1) htu
      simpa [p, mkPoint2] using h₁
  have ht₀ : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hε
  have ht₁ : t₀ + ε / 2 ∈ Metric.ball t₀ ε := by
    rw [Real.ball_eq_Ioo]
    constructor <;> linarith
  have hpoint : ∀ t ∈ Metric.ball t₀ ε, p t ∈ PlaneCurveZeroSet G := by
    intro t ht
    change MvPolynomial.eval (fun i ↦ p t i) G = 0
    exact (inline_Esgk_PlaneCurveRadialNondivisibility__eval_mkPoint2_eq_evalPlane G (γ t)).trans (hcurve t ht)
  have hne : p t₀ ≠ p (t₀ + ε / 2) := by
    intro heq
    have := hp heq
    linarith
  have hcarrier := maximallyCircular_realCarrier_not_isLineOrCircle
    hG hmax hnot (hpoint t₀ ht₀) (hpoint (t₀ + ε / 2) ht₁) hne
  have hball : (Metric.ball t₀ ε).Infinite := by
    simpa [Real.ball_eq_Ioo] using
      Set.Ioo_infinite (show t₀ - ε < t₀ + ε by linarith)
  have himage : (p '' Metric.ball t₀ ε).Infinite := Set.Infinite.image hp.injOn hball
  obtain ⟨c, hc⟩ := hconstant
  have hdist : ∀ t ∈ Metric.ball t₀ ε, dist (p t) a = dist (p t₀) a := by
    intro t ht
    have hsq := (hc t ht).trans (hc t₀ ht₀).symm
    rw [planeSquaredRadius_eq_dist_sq, planeSquaredRadius_eq_dist_sq] at hsq
    change dist (p t) a ^ 2 = dist (p t₀) a ^ 2 at hsq
    nlinarith [dist_nonneg (x := p t) (y := a), dist_nonneg (x := p t₀) (y := a)]
  have hfinite := inline_Esgk_PlaneCurveRadialNondivisibility__planeCurve_inter_sphere_finite hG hcarrier a
    (dist_nonneg (x := p t₀) (y := a))
  apply himage
  apply hfinite.subset
  rintro q ⟨t, ht, rfl⟩
  exact ⟨hpoint t ht, Metric.mem_sphere.mpr (hdist t ht)⟩

 
theorem planeRadialCritical_not_dvd_of_partial1 {G : PlanePoly}
    (hG : Irreducible G) (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ} (hz : evalPlane G z = 0)
    (hp : evalPlane (pderiv 1 G) z ≠ 0) : ¬ G ∣ planeRadialCritical G a := by
  intro hdiv
  obtain ⟨ψ, ε, hε, _hψz, hψ, hcurve, hpartial⟩ :=
    exists_regular_implicitGraph_interval_of_partial1 G hz hp
  have hradial : ∀ t ∈ Metric.ball z.1 ε,
      evalPlane (planeRadialCritical G a) (t, ψ t) = 0 :=
    fun t ht ↦ inline_Esgk_PlaneCurveRadialNondivisibility__evalPlane_eq_zero_of_dvd hdiv (hcurve t ht)
  have hconstant := planeSquaredRadius_const_of_radialCritical_eq_zero G a
    Metric.isOpen_ball Metric.isPreconnected_ball hψ.differentiableOn_one
    hcurve hpartial hradial
  exact inline_Esgk_PlaneCurveRadialNondivisibility__not_constant_radius_on_injective_interval hG hmax hnot a
    (fun t ↦ (t, ψ t)) hε (fun t u htu ↦ congrArg Prod.fst htu) hcurve hconstant

 
theorem planeRadialCritical_not_dvd_of_partial0 {G : PlanePoly}
    (hG : Irreducible G) (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ} (hz : evalPlane G z = 0)
    (hp : evalPlane (pderiv 0 G) z ≠ 0) : ¬ G ∣ planeRadialCritical G a := by
  intro hdiv
  let H : PlanePoly := rename (Equiv.swap 0 1) G
  have hzH : evalPlane H z.swap = 0 := by
    simpa only [H, Prod.swap, evalPlane_rename_swap, Prod.mk.eta] using hz
  have hpH : evalPlane (pderiv 1 H) z.swap ≠ 0 := by
    simpa only [H, evalPlane_pderiv_swap_one] using hp
  obtain ⟨ψ, ε, hε, _hψz, hψ, hcurve, hpartial⟩ :=
    exists_regular_implicitGraph_interval_of_partial1 H hzH hpH
  have hcurveG : ∀ t ∈ Metric.ball z.2 ε, evalPlane G (ψ t, t) = 0 := by
    intro t ht
    simpa only [H, evalPlane_rename_swap] using hcurve t ht
  have hradial : ∀ t ∈ Metric.ball z.2 ε,
      evalPlane (planeRadialCritical H (swapPoint a)) (t, ψ t) = 0 := by
    intro t ht
    have he := evalPlane_radialCritical_swap G a (ψ t, t)
    have hzero := inline_Esgk_PlaneCurveRadialNondivisibility__evalPlane_eq_zero_of_dvd hdiv (hcurveG t ht)
    simpa only [H, Prod.swap, hzero, neg_zero] using he
  obtain ⟨c, hc⟩ := planeSquaredRadius_const_of_radialCritical_eq_zero H (swapPoint a)
    Metric.isOpen_ball Metric.isPreconnected_ball hψ.differentiableOn_one
    hcurve hpartial hradial
  have hconstant : ∃ c : ℝ, ∀ t ∈ Metric.ball z.2 ε,
      planeSquaredRadius a (ψ t, t) = c := by
    refine ⟨c, ?_⟩
    intro t ht
    have he := planeSquaredRadius_swap a (ψ t, t)
    exact he.symm.trans (hc t ht)
  exact inline_Esgk_PlaneCurveRadialNondivisibility__not_constant_radius_on_injective_interval hG hmax hnot a
    (fun t ↦ (ψ t, t)) hε (fun t u htu ↦ congrArg Prod.snd htu) hcurveG hconstant


theorem planeRadialCritical_not_dvd_of_regular_zero {G : PlanePoly}
    (hG : Irreducible G) (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (a : PachDeZeeuw.Algebraic.Point2) {z : ℝ × ℝ} (hz : evalPlane G z = 0)
    (hregular : evalPlane (pderiv 0 G) z ≠ 0 ∨ evalPlane (pderiv 1 G) z ≠ 0) :
    ¬ G ∣ planeRadialCritical G a := by
  rcases hregular with h₀ | h₁
  · exact planeRadialCritical_not_dvd_of_partial0 hG hmax hnot a hz h₀
  · exact planeRadialCritical_not_dvd_of_partial1 hG hmax hnot a hz h₁

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem planeCurveSquaredRadiusFiber_finite_and_ncard_le
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G) (hdegree : G.totalDegree ≤ d)
    (hcarrier : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G))
    (a : PachDeZeeuw.Algebraic.Point2) (r : ℝ) :
    (planeCurveSquaredRadiusFiber G a r).Finite ∧
      (planeCurveSquaredRadiusFiber G a r).ncard ≤ 2 * d := by
  classical
  have hpos : 1 ≤ d := by
    rcases irreducible_has_nonzero_partial G hG with hp | hp
    · exact (one_le_totalDegree_of_pderiv_ne_zero G 0 hp).trans hdegree
    · exact (one_le_totalDegree_of_pderiv_ne_zero G 1 hp).trans hdegree
  have hbound : ∀ T : Finset PachDeZeeuw.Algebraic.Point2, (T : Set PachDeZeeuw.Algebraic.Point2) ⊆ planeCurveSquaredRadiusFiber G a r →
      T.card ≤ 2 * d := by
    intro T hT
    by_cases hr : 0 < r
    · have hcurve : CurveSymmetries.IsIrreducibleCurve d (PlaneCurveZeroSet G) :=
        ⟨G, hG.ne_zero, hdegree, hG, rfl⟩
      have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
      apply finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
        G a (Real.sqrt r) d T hsqrt hdegree
        (fun p hp ↦ (hT hp).1) _
        (CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
          hcurve hcarrier a hsqrt)
      intro p hp
      change dist p a = Real.sqrt r
      apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg r)).mp
      rw [Real.sq_sqrt hr.le]
      exact (hT hp).2
    · have hsingleton : T ⊆ {a} := by
        intro p hp
        simp only [Finset.mem_singleton]
        apply dist_eq_zero.mp
        have heq := (hT hp).2
        have hd : 0 ≤ dist p a := dist_nonneg
        have hrle : r ≤ 0 := le_of_not_gt hr
        nlinarith [sq_nonneg (dist p a)]
      have hcard : T.card ≤ 1 := by
        simpa only [Finset.card_singleton] using Finset.card_le_card hsingleton
      omega
  have hfinite : (planeCurveSquaredRadiusFiber G a r).Finite := by
    by_contra hinf
    obtain ⟨T, hT, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (2 * d + 1)
    have hle := hbound T hT
    omega
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  exact hbound hfinite.toFinset (by simpa only [hfinite.coe_toFinset] using
    (Set.Subset.rfl : planeCurveSquaredRadiusFiber G a r ⊆ planeCurveSquaredRadiusFiber G a r))


theorem planeCurveSquaredRadiusFiber_finite_and_ncard_le_of_maximallyCircular
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G) (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    {u v : PachDeZeeuw.Algebraic.Point2} (hu : u ∈ PlaneCurveZeroSet G) (hv : v ∈ PlaneCurveZeroSet G)
    (huv : u ≠ v) (a : PachDeZeeuw.Algebraic.Point2) (r : ℝ) :
    (planeCurveSquaredRadiusFiber G a r).Finite ∧
      (planeCurveSquaredRadiusFiber G a r).ncard ≤ 2 * d :=
  planeCurveSquaredRadiusFiber_finite_and_ncard_le hG hdegree
    (maximallyCircular_realCarrier_not_isLineOrCircle hG hmax hnot hu hv huv) a r


theorem planeCurveSquaredRadiusFiber_finite_and_ncard_le_of_sample
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G) (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G) (hsize : 2 ≤ S.card)
    (a : PachDeZeeuw.Algebraic.Point2) (r : ℝ) :
    (planeCurveSquaredRadiusFiber G a r).Finite ∧
      (planeCurveSquaredRadiusFiber G a r).ncard ≤ 2 * d := by
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  exact planeCurveSquaredRadiusFiber_finite_and_ncard_le_of_maximallyCircular
    hG hdegree hmax hnot (hS u hu) (hS v hv) huv a r

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


namespace Esgk

open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem maximallyCircular_pairSeparation_with_ncard
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmax : IsMaximallyCircular G) (hnotCircle : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hS : (S : Set PachDeZeeuw.Algebraic.Point2) ⊆ PlaneCurveZeroSet G)
    (hd : 2 ≤ G.totalDegree) :
    ∃ Δ : Finset (S × S),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * S.card ∧
      ∀ ij, ij ∉ Δ → ∀ kl, kl ∉ Δ → ij ≠ kl →
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2)
          (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2)
          (kl.2 : PachDeZeeuw.Algebraic.Point2)).Finite ∧
        (twoPairDistanceCommonZeroSet
          ⟨G, hGirreducible⟩
          (ij.1 : PachDeZeeuw.Algebraic.Point2)
          (kl.1 : PachDeZeeuw.Algebraic.Point2)
          (ij.2 : PachDeZeeuw.Algebraic.Point2)
          (kl.2 : PachDeZeeuw.Algebraic.Point2)).ncard ≤
          80 * G.totalDegree ^ 2 := by
  classical
  by_cases hsmall : S.card < 2
  · refine ⟨Finset.univ, ?_, ?_⟩
    · have hcases : S.card = 0 ∨ S.card = 1 := by omega
      rcases hcases with hzero | hone
      · simp [hzero]
      · simp [hone]
        nlinarith
    · intro ij hij
      exact False.elim (hij (Finset.mem_univ ij))
  · have hlarge : 1 < S.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlarge
    have hnot : ¬ CurveSymmetries.IsLineOrCircle (PlaneCurveZeroSet G) :=
      maximallyCircular_realCarrier_not_isLineOrCircle hGirreducible hmax
        hnotCircle (hS ha) (hS hb) hab
    obtain ⟨Δ, hΔ, hfinite⟩ := maximallyCircular_pairSeparation
      hGirreducible hmax hnotCircle S hS
    refine ⟨Δ, hΔ, ?_⟩
    intro ij hij kl hkl hne
    have hfin := hfinite ij hij kl hkl hne
    have hlabels :
        ((ij.1 : PachDeZeeuw.Algebraic.Point2),
          (ij.2 : PachDeZeeuw.Algebraic.Point2)) ≠
        ((kl.1 : PachDeZeeuw.Algebraic.Point2),
          (kl.2 : PachDeZeeuw.Algebraic.Point2)) := by
      intro heq
      apply hne
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst heq
      · apply Subtype.ext
        exact congrArg Prod.snd heq
    have hbound := twoPairDistanceCommonZeroSet_ncard_le_of_finite
      ⟨G, hGirreducible⟩ hnot
      (ij.1 : PachDeZeeuw.Algebraic.Point2)
      (kl.1 : PachDeZeeuw.Algebraic.Point2)
      (ij.2 : PachDeZeeuw.Algebraic.Point2)
      (kl.2 : PachDeZeeuw.Algebraic.Point2)
      hlabels G.totalDegree hd le_rfl hfin
    exact ⟨hfin, hbound⟩

end Esgk

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem exists_planeCurveBoundaryWitnesses_of_fiber_bounds
    (G : PlanePoly) (d : ℕ) (a b : PachDeZeeuw.Algebraic.Point2) (DA DB : Finset PachDeZeeuw.Algebraic.Point2)
    (hA : ∀ r : ℝ, (planeCurveSquaredRadiusFiber G a r).Finite ∧
      (planeCurveSquaredRadiusFiber G a r).ncard ≤ 2 * d)
    (hB : ∀ r : ℝ, (planeCurveSquaredRadiusFiber G b r).Finite ∧
      (planeCurveSquaredRadiusFiber G b r).ncard ≤ 2 * d) :
    ∃ W : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2),
      W.card ≤ 2 * d * (DA.card + DB.card) ∧
      ∀ p ∈ PlaneCurveZeroSet G, ∀ q ∈ PlaneCurveZeroSet G,
        dist p a ^ 2 = dist q b ^ 2 → p ∈ DA ∨ q ∈ DB → (p, q) ∈ W := by
  classical
  let FA : ℝ → Finset PachDeZeeuw.Algebraic.Point2 := fun r ↦ (hA r).1.toFinset
  let FB : ℝ → Finset PachDeZeeuw.Algebraic.Point2 := fun r ↦ (hB r).1.toFinset
  have hFA : ∀ r, (FA r).card ≤ 2 * d := by
    intro r
    rw [← Set.ncard_eq_toFinset_card _ (hA r).1]
    exact (hA r).2
  have hFB : ∀ r, (FB r).card ≤ 2 * d := by
    intro r
    rw [← Set.ncard_eq_toFinset_card _ (hB r).1]
    exact (hB r).2
  let L : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    DA.biUnion (fun p ↦ {p} ×ˢ FB (dist p a ^ 2))
  let R : Finset (PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2) :=
    DB.biUnion (fun q ↦ FA (dist q b ^ 2) ×ˢ {q})
  have hL : L.card ≤ DA.card * (2 * d) := by
    apply Finset.card_biUnion_le_card_mul
    intro p hp
    simpa only [Finset.card_product, Finset.card_singleton, one_mul] using hFB (dist p a ^ 2)
  have hR : R.card ≤ DB.card * (2 * d) := by
    apply Finset.card_biUnion_le_card_mul
    intro q hq
    simpa only [Finset.card_product, Finset.card_singleton, mul_one] using hFA (dist q b ^ 2)
  refine ⟨L ∪ R, ?_, ?_⟩
  · calc
      (L ∪ R).card ≤ L.card + R.card := Finset.card_union_le _ _
      _ ≤ DA.card * (2 * d) + DB.card * (2 * d) := Nat.add_le_add hL hR
      _ = 2 * d * (DA.card + DB.card) := by ring
  · intro p hp q hq heq hdistinguished
    rcases hdistinguished with hpD | hqD
    · apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hpD, Finset.mem_product.mpr ⟨Finset.mem_singleton_self p, ?_⟩⟩
      exact (hB (dist p a ^ 2)).1.mem_toFinset.mpr ⟨hq, heq.symm⟩
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨q, hqD, Finset.mem_product.mpr ⟨?_, Finset.mem_singleton_self q⟩⟩
      exact (hA (dist q b ^ 2)).1.mem_toFinset.mpr ⟨hp, heq⟩


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
theorem exists_regular_planeCurve_sample
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G)
    (hdegree : G.totalDegree ≤ d) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G)
    (hsize : d * (d - 1) < S.card) :
    ∃ p ∈ S, p ∈ PlaneCurveZeroSet G ∧ p ∉ SingularPointSet G := by
  have hfinite : (SingularPointSet G).Finite := by
    rcases irreducible_has_nonzero_partial G hG with hpartial | hpartial
    · exact (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
    · exact (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
  have hcard : (SingularPointSet G).ncard < (S : Set PachDeZeeuw.Algebraic.Point2).ncard := by
    simpa using (singularPointSet_ncard_le_degree_mul_pred hG hdegree).trans_lt hsize
  obtain ⟨p, hpS, hpregular⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hcard hfinite
  exact ⟨p, hpS, hS p hpS, hpregular⟩

 
theorem planeRadialCritical_not_dvd_of_large_sample
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G)
    (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G)
    (hsize : d * (d - 1) < S.card) (a : PachDeZeeuw.Algebraic.Point2) :
    ¬ G ∣ planeRadialCritical G a := by
  obtain ⟨p, _hpS, hpcurve, hpregular⟩ :=
    exists_regular_planeCurve_sample hG hdegree S hS hsize
  have hz : evalPlane G (chartEquiv p) = 0 :=
    (eval_eq_evalPlane_chart G p).symm.trans hpcurve
  have hregular : evalPlane (pderiv 0 G) (chartEquiv p) ≠ 0 ∨
      evalPlane (pderiv 1 G) (chartEquiv p) ≠ 0 := by
    by_contra h
    push Not at h
    apply hpregular
    change (p ∈ PlaneCurveZeroSet G ∧
      MvPolynomial.eval (fun i ↦ p i) (pderiv (0 : Fin 2) G) = 0) ∧
      MvPolynomial.eval (fun i ↦ p i) (pderiv (1 : Fin 2) G) = 0
    refine ⟨⟨hpcurve, ?_⟩, ?_⟩
    · simpa only [eval_eq_evalPlane_chart] using h.1
    · simpa only [eval_eq_evalPlane_chart] using h.2
  exact planeRadialCritical_not_dvd_of_regular_zero hG hmax hnot a hz hregular


theorem exists_planeCurve_safe_cutoff_and_critical_bounds
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G)
    (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G)
    (hsize : d * (d - 1) < S.card) :
    ∃ ε : ℝ, 0 < ε ∧ ¬ G ∣ planeGradientCutoff G ε ∧
      (∀ p ∈ S, p ∉ SingularPointSet G →
        ε < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G)) ∧
      (planeGradientCutoffZeroSet G ε).Finite ∧
      (planeGradientCutoffZeroSet G ε).ncard ≤ 2 * d * (d - 1) ∧
      ∀ a : PachDeZeeuw.Algebraic.Point2, ¬ G ∣ planeRadialCritical G a ∧
        (planeRadialCriticalZeroSet G a).Finite ∧
        (planeRadialCriticalZeroSet G a).ncard ≤ d * d := by
  have hpos : 1 ≤ G.totalDegree := by
    rcases irreducible_has_nonzero_partial G hG with hpartial | hpartial
    · exact one_le_totalDegree_of_pderiv_ne_zero G 0 hpartial
    · exact one_le_totalDegree_of_pderiv_ne_zero G 1 hpartial
  obtain ⟨ε, hε, hcut, hbelow⟩ :=
    exists_safe_positive_gradient_cutoff_level hG S hS
  have hE := planeGradientCutoffZeroSet_finite_and_ncard_le hG hdegree hpos ε hcut
  refine ⟨ε, hε, hcut, hbelow, hE.1, hE.2, ?_⟩
  intro a
  have hRa := planeRadialCritical_not_dvd_of_large_sample
    hG hdegree hmax hnot S hS hsize a
  exact ⟨hRa, planeRadialCriticalZeroSet_finite_and_ncard_le
    hG (by omega) hdegree hRa⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput auxCurve)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial


theorem maximallyCircularAuxiliaryCodegree_of_external
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d)
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmaxG : IsMaximallyCircular G) (hnotCircleG : ¬ IsCircleFactor G)
    (hcarrier : X.C₂ = PlaneCurveZeroSet G) :
    ∃ Δ : Finset (X.P₂ × X.P₂),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * X.P₂.card ∧
      ∀ pq, pq ∉ Δ → ∀ rs, rs ∉ Δ → pq ≠ rs →
        ((Finset.univ : Finset (X.P₁ × X.P₁)).filter (fun ij ↦
          auxPointPairCurveIncidence X pq ij ∧
            auxPointPairCurveIncidence X rs ij)).card ≤ 80 * d ^ 2 := by
  classical
  have hS₂ : (X.P₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆
      PlaneCurveZeroSet G := by
    simpa [hcarrier] using X.hP₂
  obtain ⟨Δ, hΔ, hpair⟩ :=
    maximallyCircular_pairSeparation_with_ncard
      hGirreducible hmaxG hnotCircleG X.P₂ hS₂
      (hmaxG.two_le_totalDegree_of_irreducible hGirreducible)
  have hzero :
      PlaneCurveZeroSet (preparedSecondCurveIrreducible X).polynomial =
        PlaneCurveZeroSet G := by
    change PlaneCurveZeroSet (preparedSecondCurvePolynomial X) =
      PlaneCurveZeroSet G
    exact (preparedSecondCurvePolynomial_zeroSet X).symm.trans hcarrier
  refine ⟨Δ, hΔ, ?_⟩
  intro pq hpq rs hrs hne
  have hfiniteG := (hpair pq hpq rs hrs hne).1
  have hfinite :
      (twoPairDistanceCommonZeroSet (preparedSecondCurveIrreducible X)
        (pq.1 : PachDeZeeuw.Algebraic.Point2)
        (rs.1 : PachDeZeeuw.Algebraic.Point2)
        (pq.2 : PachDeZeeuw.Algebraic.Point2)
        (rs.2 : PachDeZeeuw.Algebraic.Point2)).Finite := by
    simpa only [twoPairDistanceCommonZeroSet, hzero] using hfiniteG
  convert auxPointPair_twoCurveLabels_card_le X hself hd pq rs hne hfinite using 1
  congr 1

theorem maximallyCircularAuxiliaryIncidenceCount_le_of_external
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d)
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmaxG : IsMaximallyCircular G) (hnotCircleG : ¬ IsCircleFactor G)
    (hcarrier : X.C₂ = PlaneCurveZeroSet G) :
    ∃ Δ : Finset (X.P₂ × X.P₂),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * X.P₂.card ∧
      ∀ P : Finset (X.P₂ × X.P₂),
        (∀ pq ∈ P, pq ∉ Δ) →
        ∀ C : Finset (X.P₁ × X.P₁),
          (finiteIncidenceCount P C (auxPointPairCurveIncidence X) : ℝ) ≤
            (C.card : ℝ) + Real.sqrt (80 * d ^ 2) * P.card * Real.sqrt C.card := by
  classical
  obtain ⟨Δ, hΔ, hpair⟩ :=
    maximallyCircularAuxiliaryCodegree_of_external X hself hd
      hGirreducible hmaxG hnotCircleG hcarrier
  refine ⟨Δ, hΔ, ?_⟩
  intro P hP C
  suffices hbound :
      (finiteIncidenceCount P C (auxPointPairCurveIncidence X) : ℝ) ≤
        (C.card : ℝ) + Real.sqrt (↑(80 * d ^ 2 : ℕ) : ℝ) * P.card *
          Real.sqrt C.card by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hbound
  apply finiteIncidenceCount_le_of_codegree P C
    (auxPointPairCurveIncidence X) (80 * d ^ 2)
  intro pq hpq rs hrs hne
  have hfull := hpair pq (hP pq hpq) rs (hP rs hrs) hne
  have hsubset :
      C.filter (fun ij ↦
        auxPointPairCurveIncidence X pq ij ∧
          auxPointPairCurveIncidence X rs ij) ⊆
        (Finset.univ : Finset (X.P₁ × X.P₁)).filter (fun ij ↦
          auxPointPairCurveIncidence X pq ij ∧
            auxPointPairCurveIncidence X rs ij) := by
    intro ij hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2⟩
  exact (Finset.card_le_card hsubset).trans hfull

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


private theorem inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval (P : PlanePoly) :
    Continuous (fun p : PachDeZeeuw.Algebraic.Point2 ↦ MvPolynomial.eval (fun i ↦ p i) P) :=
  (MvPolynomial.continuous_eval P).comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ))

 
theorem isOpen_planeCurveSafeSet (G : PlanePoly) (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2) :
    IsOpen (planeCurveSafeSet G ε a) := by
  change IsOpen ({p : planeCurveRegularLocus G |
    ε < MvPolynomial.eval (fun i ↦ (p : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G)} ∩
    {p | MvPolynomial.eval (fun i ↦ (p : PachDeZeeuw.Algebraic.Point2) i) (planeRadialCritical G a) ≠ 0})
  exact (isOpen_lt continuous_const
    ((inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval _).comp continuous_subtype_val)).inter
    (isClosed_eq ((inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval _).comp continuous_subtype_val)
      continuous_const).isOpen_compl

 
theorem disjoint_planeCurveSafeSet_boundary (G : PlanePoly) (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2) :
    Disjoint (planeCurveSafeSet G ε a) (planeCurveSafeBoundary G ε a) := by
  rw [Set.disjoint_left]
  intro p hp hb
  rcases hb with hlevel | hcritical
  · exact (ne_of_gt hp.1) hlevel
  · exact hp.2 hcritical

 
theorem frontier_planeCurveSafeSet_subset_boundary
    (G : PlanePoly) (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2) :
    frontier (planeCurveSafeSet G ε a) ⊆ planeCurveSafeBoundary G ε a := by
  intro p hp
  rw [frontier, (isOpen_planeCurveSafeSet G ε a).interior_eq] at hp
  have hclosed : IsClosed {q : planeCurveRegularLocus G |
      ε ≤ MvPolynomial.eval (fun i ↦ (q : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G)} :=
    isClosed_le continuous_const ((inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval _).comp continuous_subtype_val)
  have hle : ε ≤ MvPolynomial.eval (fun i ↦ (p : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G) :=
    closure_minimal (fun _ hq ↦ hq.1.le) hclosed hp.1
  by_cases hcritical : (p : PachDeZeeuw.Algebraic.Point2) ∈ PlaneCurveZeroSet (planeRadialCritical G a)
  · exact Or.inr hcritical
  · apply Or.inl
    apply le_antisymm _ hle
    by_contra h
    exact hp.2 ⟨lt_of_not_ge h, hcritical⟩


theorem exists_planeCurveSafe_closure_radius_minimum
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (a : PachDeZeeuw.Algebraic.Point2)
    (C : Set (planeCurveRegularLocus G)) (hC : C.Nonempty)
    (hCsafe : C ⊆ planeCurveSafeSet G ε a) :
    ∃ p ∈ closure C, ∀ q ∈ C, dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2 ≤ dist (q : PachDeZeeuw.Algebraic.Point2) a ^ 2 := by
  let A : Set PachDeZeeuw.Algebraic.Point2 := Subtype.val '' C
  obtain ⟨q₀, hq₀⟩ := hC
  have hqA : (q₀ : PachDeZeeuw.Algebraic.Point2) ∈ A := ⟨q₀, hq₀, rfl⟩
  obtain ⟨p, hp, _, _, _, hmin⟩ := exists_minimizing_equalDistance_pair a a A A
    ⟨q₀, hqA, q₀, hqA, rfl⟩
  have hGclosed : IsClosed (PlaneCurveZeroSet G) :=
    isClosed_eq (inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval G) continuous_const
  have hAG : A ⊆ PlaneCurveZeroSet G := by
    rintro _ ⟨q, _, rfl⟩
    exact q.property.1
  have hpG : p ∈ PlaneCurveZeroSet G := closure_minimal hAG hGclosed hp
  have hQclosed : IsClosed {q : PachDeZeeuw.Algebraic.Point2 |
      ε ≤ MvPolynomial.eval (fun i ↦ q i) (planeGradientSquare G)} :=
    isClosed_le continuous_const (inline_Esgk_PlaneCurveSafeComponents__continuous_planeCurveEval _)
  have hAQ : A ⊆ {q : PachDeZeeuw.Algebraic.Point2 |
      ε ≤ MvPolynomial.eval (fun i ↦ q i) (planeGradientSquare G)} := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hCsafe hq).1.le
  have hpQ : ε ≤ MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) :=
    closure_minimal hAQ hQclosed hp
  have hpregular : p ∉ SingularPointSet G :=
    (planeGradientSquare_eval_pos_iff_not_mem_singular hpG).mp (hε.trans_le hpQ)
  refine ⟨⟨p, hpG, hpregular⟩, ?_, ?_⟩
  · rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hp
  · intro q hq
    have hqA' : (q : PachDeZeeuw.Algebraic.Point2) ∈ A := ⟨q, hq, rfl⟩
    have hbound := hmin q hqA' q hqA' rfl
    exact pow_le_pow_left₀ dist_nonneg hbound 2

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput Point4 auxCurve auxPointSet)

theorem finiteIncidenceCount_univ_auxPointPairCurveIncidence_eq_auxIncidences_card
    {d : ℕ} (X : PreparedBipartiteInput d) :
    finiteIncidenceCount
        (Finset.univ : Finset (X.P₂ × X.P₂))
        (Finset.univ : Finset (X.P₁ × X.P₁))
        (auxPointPairCurveIncidence X) =
      (PachDeZeeuw.auxIncidences X).card := by
  classical
  rw [finiteIncidenceCount_eq_card_filter_product, PachDeZeeuw.auxIncidences]
  refine Finset.card_bij
    (fun (a : (X.P₂ × X.P₂) × (X.P₁ × X.P₁)) _ ↦ (encodedAuxPoint
      ((a.1.1 : PachDeZeeuw.Algebraic.Point2),
        (a.1.2 : PachDeZeeuw.Algebraic.Point2)), a.2)) ?_ ?_ ?_
  · intro a ha
    have ha' := Finset.mem_filter.mp ha
    let pq : PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 :=
      (a.1.1, a.1.2)
    have hpq : pq ∈ X.P₂.product X.P₂ :=
      Finset.mem_product.mpr ⟨a.1.1.property, a.1.2.property⟩
    have hpoint : encodedAuxPoint pq ∈ auxPointSet X := by
      dsimp [auxPointSet]
      exact Finset.mem_image.mpr ⟨pq, hpq, rfl⟩
    have hlabel : a.2 ∈ (Finset.univ : Finset (X.P₁ × X.P₁)) :=
      Finset.mem_univ _
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hpoint, hlabel⟩
    · exact ha'.2
  · intro a₁ ha₁ a₂ ha₂ hEq
    have hpq :
        ((a₁.1.1 : PachDeZeeuw.Algebraic.Point2),
          (a₁.1.2 : PachDeZeeuw.Algebraic.Point2)) =
        ((a₂.1.1 : PachDeZeeuw.Algebraic.Point2),
          (a₂.1.2 : PachDeZeeuw.Algebraic.Point2)) :=
      encodedAuxPoint_injective (congrArg Prod.fst hEq)
    apply Prod.ext
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst hpq))
        (Subtype.ext (congrArg Prod.snd hpq))
    · exact congrArg (fun z : Point4 × (X.P₁ × X.P₁) ↦ z.2) hEq
  · intro b hb
    have hb' := Finset.mem_filter.mp hb
    have hpoint : b.1 ∈ auxPointSet X :=
      (Finset.mem_product.mp hb'.1).1
    obtain ⟨pq, hpq, hencode⟩ :=
      exists_encodedAuxPoint_eq_of_mem_auxPointSet X hpoint
    have hpq' := Finset.mem_product.mp hpq
    let pqlabel : X.P₂ × X.P₂ :=
      (⟨pq.1, hpq'.1⟩, ⟨pq.2, hpq'.2⟩)
    have hbcurve : encodedAuxPoint pq ∈ auxCurve X b.2.1 b.2.2 := by
      rw [hencode]
      exact hb'.2
    have hrel : auxPointPairCurveIncidence X pqlabel b.2 := by
      simpa [auxPointPairCurveIncidence, pqlabel] using hbcurve
    have hsource :
        ((pqlabel, b.2) :
          (X.P₂ × X.P₂) × (X.P₁ × X.P₁)) ∈
          ((Finset.univ : Finset (X.P₂ × X.P₂)).product
            (Finset.univ : Finset (X.P₁ × X.P₁))).filter
            (fun a ↦ auxPointPairCurveIncidence X a.1 a.2) := by
      refine Finset.mem_filter.mpr ⟨?_, hrel⟩
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩
    refine ⟨⟨pqlabel, b.2⟩, hsource, ?_⟩
    apply Prod.ext
    · simpa [pqlabel] using hencode
    · rfl

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open EuclideanGeometry
open PachDeZeeuw (PreparedBipartiteInput auxCurve)
open PachDeZeeuw.Algebraic (PlaneCurveZeroSet mem_PlaneCurveZeroSet)

private theorem inline_Esgk_AuxiliaryPointPairFiberBound__auxPointPairCurveIncidence_sqDistance {d : ℕ}
    (X : PreparedBipartiteInput d) (pq : X.P₂ × X.P₂)
    (ij : X.P₁ × X.P₁)
    (hinc : auxPointPairCurveIncidence X pq ij) :
    dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
        (pq.1 : PachDeZeeuw.Algebraic.Point2) ^ 2 =
      dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
        (pq.2 : PachDeZeeuw.Algebraic.Point2) ^ 2 := by
  have hcurve : encodedAuxPoint
      ((pq.1 : PachDeZeeuw.Algebraic.Point2),
        (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈
      auxCurve X ij.1 ij.2 := hinc
  have hsq := hcurve.2.2
  change dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxFirst (encodedAuxPoint
        ((pq.1 : PachDeZeeuw.Algebraic.Point2),
          (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 =
    dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxSecond (encodedAuxPoint
        ((pq.1 : PachDeZeeuw.Algebraic.Point2),
          (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 at hsq
  simpa using hsq

theorem auxPointPairCurveIncidence_label_card_le
    {d : ℕ} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X)
    (pq : X.P₂ × X.P₂) :
    ((Finset.univ : Finset (X.P₁ × X.P₁)).filter
      (auxPointPairCurveIncidence X pq)).card ≤ 2 * d * X.P₁.card := by
  classical
  let labels : Finset (X.P₁ × X.P₁) :=
    (Finset.univ : Finset (X.P₁ × X.P₁)).filter
      (auxPointPairCurveIncidence X pq)
  let circleFiber (i : X.P₁) : Finset PachDeZeeuw.Algebraic.Point2 :=
    X.P₁.filter (fun j ↦
      dist (pq.2 : PachDeZeeuw.Algebraic.Point2)
          (j : PachDeZeeuw.Algebraic.Point2) =
        dist (i : PachDeZeeuw.Algebraic.Point2)
          (pq.1 : PachDeZeeuw.Algebraic.Point2))
  let labelFiber (i : X.P₁) : Finset (X.P₁ × X.P₁) :=
    labels.filter (fun ij ↦ ij.1 = i)
  have hnot : ¬ CurveSymmetries.IsLineOrCircle X.C₂ :=
    selfCurvePreparedInput_not_isLineOrCircle hself
  have hcircle : ∀ i : X.P₁, (circleFiber i).card ≤ 2 * d := by
    intro i
    have hr : 0 < dist (i : PachDeZeeuw.Algebraic.Point2)
        (pq.1 : PachDeZeeuw.Algebraic.Point2) :=
      prepared_first_second_dist_pos X i pq.1.property
    have hzero : ∀ z ∈ circleFiber i,
        MvPolynomial.eval (fun k ↦ z k)
          (preparedSecondCurvePolynomial X) = 0 := by
      intro z hz
      have hz' := Finset.mem_filter.mp hz
      have hzC₁ : z ∈ X.C₁ :=
        X.hP₁ hz'.1
      have hzC₂ : (z : PachDeZeeuw.Algebraic.Point2) ∈ X.C₂ := by
        rw [hself] at hzC₁
        exact hzC₁
      have hzZero : (z : PachDeZeeuw.Algebraic.Point2) ∈
          PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := by
        rw [← preparedSecondCurvePolynomial_zeroSet X]
        exact hzC₂
      rw [mem_PlaneCurveZeroSet] at hzZero
      exact hzZero
    have hcircleMem : ∀ z ∈ circleFiber i,
        (z : PachDeZeeuw.Algebraic.Point2) ∈
          Metric.sphere (pq.2 : PachDeZeeuw.Algebraic.Point2)
            (dist (i : PachDeZeeuw.Algebraic.Point2)
              (pq.1 : PachDeZeeuw.Algebraic.Point2)) := by
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      apply Metric.mem_sphere.mpr
      simpa [dist_comm] using hz'
    have hnotSphere : ¬ Metric.sphere
        (pq.2 : PachDeZeeuw.Algebraic.Point2)
          (dist (i : PachDeZeeuw.Algebraic.Point2)
            (pq.1 : PachDeZeeuw.Algebraic.Point2)) ⊆
        PlaneCurveZeroSet (preparedSecondCurvePolynomial X) := by
      rw [← preparedSecondCurvePolynomial_zeroSet X]
      exact CurveSymmetries.sphere_not_subset_of_irreducibleCurve_not_lineOrCircle
        (preparedSecondCurve_isIrreducibleCurve X) hnot
        (pq.2 : PachDeZeeuw.Algebraic.Point2) hr
    exact finite_circle_zeroSet_card_le_two_mul_of_not_sphere_subset
      (preparedSecondCurvePolynomial X)
      (pq.2 : PachDeZeeuw.Algebraic.Point2)
      (dist (i : PachDeZeeuw.Algebraic.Point2)
        (pq.1 : PachDeZeeuw.Algebraic.Point2)) d (circleFiber i) hr
      (preparedSecondCurvePolynomial_totalDegree_le X) hzero hcircleMem
      hnotSphere
  have hfiber : ∀ i : X.P₁, (labelFiber i).card ≤ 2 * d := by
    intro i
    apply (Finset.card_le_card_of_injOn
      (fun ij ↦ (ij.2 : PachDeZeeuw.Algebraic.Point2)) ?_ ?_).trans
      (hcircle i)
    · intro ij hij
      have hinc := (Finset.mem_filter.mp (Finset.mem_filter.mp hij).1).2
      have hsq := inline_Esgk_AuxiliaryPointPairFiberBound__auxPointPairCurveIncidence_sqDistance X pq ij hinc
      have hnonneg₁ : 0 ≤ dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
          (pq.1 : PachDeZeeuw.Algebraic.Point2) := dist_nonneg
      have hnonneg₂ : 0 ≤ dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
          (pq.2 : PachDeZeeuw.Algebraic.Point2) := dist_nonneg
      have hdist : dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
          (pq.1 : PachDeZeeuw.Algebraic.Point2) =
          dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
            (pq.2 : PachDeZeeuw.Algebraic.Point2) := by
        nlinarith
      apply Finset.mem_filter.mpr
      exact ⟨ij.2.property, by
        have hfirst := (Finset.mem_filter.mp hij).2
        rw [hfirst] at hdist
        simpa [dist_comm] using hdist.symm⟩
    · intro ij hij kl hkl heq
      have hfirst : ij.1 = i := (Finset.mem_filter.mp hij).2
      have hfirst' : kl.1 = i := (Finset.mem_filter.mp hkl).2
      apply Prod.ext (hfirst.trans hfirst'.symm)
      exact Subtype.ext heq
  have hcover : labels ⊆
      (Finset.univ : Finset X.P₁).biUnion labelFiber := by
    intro ij hij
    apply Finset.mem_biUnion.mpr
    refine ⟨ij.1, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨hij, rfl⟩
  change labels.card ≤ 2 * d * X.P₁.card
  calc
    labels.card ≤ ((Finset.univ : Finset X.P₁).biUnion labelFiber).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ i ∈ (Finset.univ : Finset X.P₁), (labelFiber i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ (Finset.univ : Finset X.P₁), 2 * d := by
      exact Finset.sum_le_sum fun i _ ↦ hfiber i
    _ = 2 * d * X.P₁.card := by simp [Nat.mul_comm, Nat.mul_assoc]

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

open scoped Classical

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)
open IrreduciblePlanePolynomial

theorem maximallyCircularCellIncidence_of_external
    {d : ℕ} {ι : Type*} (X : PreparedBipartiteInput d)
    (hself : SelfCurvePreparedInput X) (hd : 2 ≤ d)
    {G : PlanePoly} (hGirreducible : Irreducible G)
    (hmaxG : IsMaximallyCircular G) (hnotCircleG : ¬ IsCircleFactor G)
    (hcarrier : X.C₂ = PlaneCurveZeroSet G) :
    ∃ Δ : Finset (X.P₂ × X.P₂),
      Δ.card ≤ 8 * G.totalDegree ^ 2 * X.P₂.card ∧
      ∀ (cells : Finset ι)
        (P : ι → Finset (X.P₂ × X.P₂))
        (C : ι → Finset (X.P₁ × X.P₁))
        (L R T : ℝ),
        (∀ ω ∈ cells, Disjoint (P ω) Δ) →
        0 ≤ L →
        (cells.card : ℝ) ≤ R →
        (∑ ω ∈ cells, ((C ω).card : ℝ)) ≤ T →
        (∀ ω ∈ cells, ((P ω).card : ℝ) ≤ L) →
        (∑ ω ∈ cells,
            (finiteIncidenceCount (P ω) (C ω)
              (auxPointPairCurveIncidence X) : ℝ)) ≤
          Real.sqrt (↑(80 * d ^ 2 : ℕ) : ℝ) * L * Real.sqrt (R * T) + T := by
  classical
  obtain ⟨Δ, hΔ, hcodegree⟩ :=
    maximallyCircularAuxiliaryIncidenceCount_le_of_external X hself hd
      hGirreducible hmaxG hnotCircleG hcarrier
  refine ⟨Δ, hΔ, ?_⟩
  intro cells P C L R T hdisjoint hL hR hT hpoints
  have hlocal : ∀ ω ∈ cells,
      (finiteIncidenceCount (P ω) (C ω)
        (auxPointPairCurveIncidence X) : ℝ) ≤
        Real.sqrt (↑(80 * d ^ 2 : ℕ) : ℝ) * (P ω).card *
            Real.sqrt ((C ω).card) + (C ω).card := by
    intro ω hω
    have hPω : ∀ pq ∈ P ω, pq ∉ Δ := by
      intro pq hpq
      intro hpqΔ
      exact (Finset.disjoint_left.1 (hdisjoint ω hω)) hpq hpqΔ
    have hbound := hcodegree (P ω) hPω (C ω)
    simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hbound
  exact finiteCellIncidenceSum_le cells
    (fun ω ↦ finiteIncidenceCount (P ω) (C ω)
      (auxPointPairCurveIncidence X))
    (fun ω ↦ (P ω).card)
    (fun ω ↦ (C ω).card)
    (80 * d ^ 2) L R T hL hR hT hpoints hlocal


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem planeCurveExceptionalSample_card_le
    {G : PlanePoly} {d : ℕ} (hG : Irreducible G)
    (hdegree : G.totalDegree ≤ d) (a : PachDeZeeuw.Algebraic.Point2) (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hcritical : (planeRadialCriticalZeroSet G a).Finite)
    (hcritical_card : (planeRadialCriticalZeroSet G a).ncard ≤ d * d) :
    (planeCurveExceptionalSample G a S).card ≤ 2 * d ^ 2 := by
  classical
  have hsingular : (SingularPointSet G).Finite := by
    rcases irreducible_has_nonzero_partial G hG with hpartial | hpartial
    · exact (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
    · exact (finite_singularities_of_irreducible_bound G hG hdegree hpartial).1
  have hsub : (planeCurveExceptionalSample G a S : Set PachDeZeeuw.Algebraic.Point2) ⊆
      SingularPointSet G ∪ planeRadialCriticalZeroSet G a := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hcard := Set.ncard_le_ncard hsub (hsingular.union hcritical)
  have hsingular_card := singularPointSet_ncard_le_degree_mul_pred hG hdegree
  have hpred : d * (d - 1) ≤ d * d := Nat.mul_le_mul_left d (Nat.sub_le d 1)
  calc
    (planeCurveExceptionalSample G a S).card ≤
        (SingularPointSet G ∪ planeRadialCriticalZeroSet G a).ncard := by
      simpa using hcard
    _ ≤ (SingularPointSet G).ncard + (planeRadialCriticalZeroSet G a).ncard :=
      Set.ncard_union_le _ _
    _ ≤ d * (d - 1) + d * d := Nat.add_le_add hsingular_card hcritical_card
    _ ≤ 2 * d ^ 2 := by nlinarith


theorem exceptional_ordered_pairs_card_le
    {α : Type*} [DecidableEq α] (S B : Finset α) {d : ℕ}
    (hB : B.card ≤ 2 * d ^ 2) :
    ((B ×ˢ S) ∪ (S ×ˢ B)).card ≤ 4 * d ^ 2 * S.card := by
  calc
    ((B ×ˢ S) ∪ (S ×ˢ B)).card ≤ (B ×ˢ S).card + (S ×ˢ B).card :=
      Finset.card_union_le _ _
    _ = B.card * S.card + S.card * B.card := by simp only [Finset.card_product]
    _ ≤ 4 * d ^ 2 * S.card := by nlinarith

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
theorem locallyConnectedSpace_planeCurveRegularLocus (G : PlanePoly) :
    LocallyConnectedSpace (planeCurveRegularLocus G) :=
  locallyConnectedSpace_of_real_charts (fun x ↦ by
    obtain ⟨i, e, hx, _⟩ := exists_planeCurveRegular_chart G x
    exact ⟨e, hx⟩)

 
theorem isLocalHomeomorph_planeCurveSafe_squaredRadius
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (a : PachDeZeeuw.Algebraic.Point2) :
    IsLocalHomeomorph (fun p : planeCurveSafeSet G ε a ↦
      dist ((p : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2) := by
  let M := planeCurveRegularLocus G
  let U := planeCurveSafeSet G ε a
  let R := planeCurveRadialRegularLocus G a
  let ι : U → R := fun p ↦ ⟨((p : M) : PachDeZeeuw.Algebraic.Point2), p.val.property.1, p.property.2⟩
  have hval : Topology.IsEmbedding (fun p : U ↦ ((p : M) : PachDeZeeuw.Algebraic.Point2)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hi : Topology.IsEmbedding ι :=
    hval.codRestrict R (fun p ↦ ⟨p.val.property.1, p.property.2⟩)
  have hrange : Set.range ι = {p : R |
      ε < MvPolynomial.eval (fun i ↦ (p : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G)} := by
    ext p
    constructor
    · rintro ⟨q, rfl⟩
      exact q.property.1
    · intro hp
      have hregular : (p : PachDeZeeuw.Algebraic.Point2) ∉ SingularPointSet G :=
        (planeGradientSquare_eval_pos_iff_not_mem_singular p.property.1).mp (hε.trans hp)
      let q : M := ⟨p, p.property.1, hregular⟩
      exact ⟨⟨q, hp, p.property.2⟩, rfl⟩
  have hopen : IsOpen (Set.range ι) := by
    rw [hrange]
    exact isOpen_lt continuous_const
      (((MvPolynomial.continuous_eval (planeGradientSquare G)).comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ))).comp continuous_subtype_val)
  have hopenι : Topology.IsOpenEmbedding ι :=
    { toIsEmbedding := hi, isOpen_range := hopen }
  have hcomp : IsLocalHomeomorph ((fun p : R ↦ dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2) ∘ ι) :=
    (isLocalHomeomorph_planeCurve_squaredRadius G a).comp hopenι.isLocalHomeomorph
  exact hcomp


theorem exists_planeCurveSafe_component_boundary
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (a : PachDeZeeuw.Algebraic.Point2)
    {x : planeCurveRegularLocus G} (hx : x ∈ planeCurveSafeSet G ε a) :
    ∃ p ∈ planeCurveSafeBoundary G ε a,
      p ∈ closure (connectedComponentIn (planeCurveSafeSet G ε a) x) := by
  let : LocallyConnectedSpace (planeCurveRegularLocus G) :=
    locallyConnectedSpace_planeCurveRegularLocus G
  have hminimum := exists_planeCurveSafe_closure_radius_minimum G hε a
    (connectedComponentIn (planeCurveSafeSet G ε a) x)
    ⟨x, mem_connectedComponentIn hx⟩
    (connectedComponentIn_subset _ _)
  obtain ⟨p, hpclosure, hpfrontier⟩ :=
    exists_connectedComponentIn_frontier_of_closure_minimum
      (isOpen_planeCurveSafeSet G ε a) (fun p ↦ dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2)
      (isLocalHomeomorph_planeCurveSafe_squaredRadius G hε a) hminimum
  exact ⟨p, frontier_planeCurveSafeSet_subset_boundary G ε a hpfrontier, hpclosure⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open Filter PachDeZeeuw.Algebraic
open PachDeZeeuw (PreparedBipartiteInput)

private theorem inline_Esgk_MaximallyCircularLargeScaleIncidence__auxIncidences_card_le_two_degree_mul_card_cube
    {d : ℕ} {S : Finset PachDeZeeuw.Algebraic.Point2}
    (X : PreparedBipartiteInput d)
    (hP₁ : (X.P₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S)
    (hP₂ : (X.P₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S) :
    (PachDeZeeuw.auxIncidences X).card ≤ 2 * d * S.card ^ 3 := by
  classical
  let labels : Finset (X.P₁ × X.P₁) := Finset.univ
  have hlabels : labels.card = X.P₁.card ^ 2 := by
    simp [labels, pow_two]
  have hfiber : ∀ ij ∈ labels,
      (auxIncidencesWithCurveLabel X ij).card ≤
        2 * d * X.P₂.card := by
    intro ij _
    exact auxIncidencesWithCurveLabel_card_le_sharp X ij
  have hcard := auxIncidencesOverCurveLabels_card_le X labels hfiber
  have hall : auxIncidencesOverCurveLabels X labels =
      PachDeZeeuw.auxIncidences X := by
    ext incidence
    simp [labels, auxIncidencesOverCurveLabels]
  have hp₁set : X.P₁ ⊆ S := by
    intro p hp
    exact hP₁ hp
  have hp₂set : X.P₂ ⊆ S := by
    intro p hp
    exact hP₂ hp
  have hp₁ : X.P₁.card ≤ S.card := Finset.card_le_card hp₁set
  have hp₂ : X.P₂.card ≤ S.card := Finset.card_le_card hp₂set
  have hprod : X.P₁.card ^ 2 * X.P₂.card ≤ S.card ^ 2 * S.card := by
    exact Nat.mul_le_mul
      (Nat.pow_le_pow_left hp₁ 2) hp₂
  rw [← hall]
  calc
    (auxIncidencesOverCurveLabels X labels).card ≤
        labels.card * (2 * d * X.P₂.card) := hcard
    _ = 2 * d * (X.P₁.card ^ 2 * X.P₂.card) := by
      rw [hlabels]
      ring
    _ ≤ 2 * d * (S.card ^ 2 * S.card) :=
      Nat.mul_le_mul_left _ hprod
    _ = 2 * d * S.card ^ 3 := by ring

private theorem inline_Esgk_MaximallyCircularLargeScaleIncidence__finiteIncidenceCount_card_le_two_degree_mul_card_cube
    {d : ℕ} {S : Finset PachDeZeeuw.Algebraic.Point2}
    (X : PreparedBipartiteInput d)
    (hP₁ : (X.P₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S)
    (hP₂ : (X.P₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S) :
    (finiteIncidenceCount
      (Finset.univ : Finset (X.P₂ × X.P₂))
      (Finset.univ : Finset (X.P₁ × X.P₁))
      (auxPointPairCurveIncidence X) : ℝ) ≤
      (2 : ℝ) * d * S.card ^ 3 := by
  rw [finiteIncidenceCount_univ_auxPointPairCurveIncidence_eq_auxIncidences_card]
  exact_mod_cast inline_Esgk_MaximallyCircularLargeScaleIncidence__auxIncidences_card_le_two_degree_mul_card_cube X hP₁ hP₂


theorem maximallyCircularRestrictedRawAuxiliaryIncidence_to_raw
    (hRestricted : MaximallyCircularRestrictedRawAuxiliaryIncidenceStatement) :
    MaximallyCircularRawAuxiliaryIncidenceStatement := by
  classical
  rcases hRestricted with ⟨K, hK, hEstimate⟩
  let K' : ℕ := max K 2
  have hKle : K ≤ K' := by
    exact Nat.le_max_left _ _
  have h2le : 2 ≤ K' := by
    exact Nat.le_max_right _ _
  have hK'pos : 1 ≤ K' := by omega
  refine ⟨K', hK'pos, ?_⟩
  intro G S X hG hGabs hNotCircle hMax hS hSelf hC₂ hDisjoint hUnion
    hP₁ hP₂ hPos j hj
  have hP₁sub : (X.P₁ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S := by
    intro p hp
    have hp' : p ∈ X.P₁ ∪ X.P₂ := Finset.mem_union.mpr (Or.inl hp)
    rw [hUnion] at hp'
    exact hp'
  have hP₂sub : (X.P₂ : Set PachDeZeeuw.Algebraic.Point2) ⊆ S := by
    intro p hp
    have hp' : p ∈ X.P₁ ∪ X.P₂ := Finset.mem_union.mpr (Or.inr hp)
    rw [hUnion] at hp'
    exact hp'
  let B : ℝ :=
    (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 / Real.sqrt (j : ℝ) +
      (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 +
      (S.card : ℝ) ^ 2 +
      (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
      (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2
  have hBnonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  by_cases hsmall : j * G.totalDegree < S.card
  · have hsmallBound := hEstimate G S X hG hGabs hNotCircle hMax hS hSelf
      hC₂ hDisjoint hUnion hP₁ hP₂ hPos j hj hsmall
    have hKreal : (K : ℝ) ≤ (K' : ℝ) := by
      exact_mod_cast hKle
    have hcoef := mul_le_mul_of_nonneg_right hKreal hBnonneg
    exact hsmallBound.trans (by simpa [B, K'] using hcoef)
  · have hlarge : S.card ≤ j * G.totalDegree := by omega
    have hlargeR : (S.card : ℝ) ≤ (j : ℝ) * G.totalDegree := by
      exact_mod_cast hlarge
    have hcount := inline_Esgk_MaximallyCircularLargeScaleIncidence__finiteIncidenceCount_card_le_two_degree_mul_card_cube X
      hP₁sub hP₂sub
    have hterm :
        (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 ≤
          (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hlargeR
        (by positivity : 0 ≤ (G.totalDegree : ℝ) * (S.card : ℝ) ^ 2)
      calc
        (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 =
            (G.totalDegree : ℝ) * (S.card : ℝ) ^ 2 * (S.card : ℝ) := by ring
        _ ≤ (G.totalDegree : ℝ) * (S.card : ℝ) ^ 2 *
            ((j : ℝ) * G.totalDegree) := hmul
        _ = (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 := by ring
    have htwoterm :
        (2 : ℝ) * (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 ≤ 2 * B := by
      have := mul_le_mul_of_nonneg_left hterm (by norm_num : (0 : ℝ) ≤ 2)
      have hrest : 0 ≤
          (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 / Real.sqrt (j : ℝ) +
            (S.card : ℝ) ^ 2 +
            (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
            (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2 := by
        positivity
      dsimp [B]
      calc
        (2 : ℝ) * (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 ≤
            2 * ((G.totalDegree : ℝ) ^ 2 * (j : ℝ) *
              (S.card : ℝ) ^ 2) := by
          simpa [mul_assoc] using this
        _ ≤ 2 * ((G.totalDegree : ℝ) ^ 2 * (j : ℝ) *
              (S.card : ℝ) ^ 2 +
            ((G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 /
                Real.sqrt (j : ℝ) +
              (S.card : ℝ) ^ 2 +
              (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
              (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hrest)
            (by norm_num)
        _ = 2 * B := by ring
    have hcoef : (2 : ℝ) ≤ (K' : ℝ) := by
      exact_mod_cast h2le
    have hcoefB := mul_le_mul_of_nonneg_right hcoef hBnonneg
    calc
      (finiteIncidenceCount
          (Finset.univ : Finset (X.P₂ × X.P₂))
          (Finset.univ : Finset (X.P₁ × X.P₁))
          (auxPointPairCurveIncidence X) : ℝ) ≤
          (2 : ℝ) * (G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 := hcount
      _ ≤ 2 * B := htwoterm
      _ ≤ (K' : ℝ) * B := hcoefB
      _ = (K' : ℝ) * ((G.totalDegree : ℝ) * (S.card : ℝ) ^ 3 /
          Real.sqrt (j : ℝ) +
        (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2 +
        (S.card : ℝ) ^ 2 +
        (G.totalDegree : ℝ) ^ 4 * (j : ℝ) ^ 2 +
        (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2) := by rfl

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

private theorem inline_Esgk_PlaneCurveArcRadiusWitness__continuous_arcPolynomialEval (P : PlanePoly) :
    Continuous (fun p : PachDeZeeuw.Algebraic.Point2 ↦ MvPolynomial.eval (fun i ↦ p i) P) :=
  (MvPolynomial.continuous_eval P).comp
    (PiLp.continuous_ofLp 2 (fun _ : Fin 2 ↦ ℝ))

 
theorem mem_planeCurveRegularLocus_of_mem_closure_safe_image
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (o : PachDeZeeuw.Algebraic.Point2)
    {A : Set (planeCurveRegularLocus G)} (hA : A ⊆ planeCurveSafeSet G ε o)
    {p : PachDeZeeuw.Algebraic.Point2} (hp : p ∈ closure (Subtype.val '' A)) :
    p ∈ planeCurveRegularLocus G := by
  have hGclosed : IsClosed (PlaneCurveZeroSet G) :=
    isClosed_eq (inline_Esgk_PlaneCurveArcRadiusWitness__continuous_arcPolynomialEval G) continuous_const
  have hcurve : p ∈ PlaneCurveZeroSet G := by
    apply closure_minimal _ hGclosed hp
    rintro _ ⟨q, _, rfl⟩
    exact q.property.1
  have hQclosed : IsClosed {q : PachDeZeeuw.Algebraic.Point2 |
      ε ≤ MvPolynomial.eval (fun i ↦ q i) (planeGradientSquare G)} :=
    isClosed_le continuous_const (inline_Esgk_PlaneCurveArcRadiusWitness__continuous_arcPolynomialEval _)
  have hQ : ε ≤ MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G) := by
    apply closure_minimal _ hQclosed hp
    rintro _ ⟨q, hq, rfl⟩
    exact (hA hq).1.le
  exact ⟨hcurve,
    (planeGradientSquare_eval_pos_iff_not_mem_singular hcurve).mp (hε.trans_le hQ)⟩


theorem planeCurveRegular_radius_mem_interior_image
    (G : PlanePoly) (a : PachDeZeeuw.Algebraic.Point2) {A : Set (planeCurveRegularLocus G)}
    (hA : IsOpen A) {p : planeCurveRegularLocus G} (hp : p ∈ A)
    (hcritical : (p : PachDeZeeuw.Algebraic.Point2) ∉ planeRadialCriticalZeroSet G a) :
    dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2 ∈
      interior ((fun q : PachDeZeeuw.Algebraic.Point2 ↦ dist q a ^ 2) '' (Subtype.val '' A)) := by
  let Qp := MvPolynomial.eval (fun i ↦ (p : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G)
  have hQp : 0 < Qp :=
    (planeGradientSquare_eval_pos_iff_not_mem_singular p.property.1).mpr p.property.2
  let ε := Qp / 2
  have hε : 0 < ε := half_pos hQp
  have hpU : p ∈ planeCurveSafeSet G ε a := by
    refine ⟨half_lt_self hQp, ?_⟩
    intro hzero
    exact hcritical ⟨p.property.1, hzero⟩
  let U := planeCurveSafeSet G ε a
  let V : Set U := {q | (q : planeCurveRegularLocus G) ∈ A}
  let f : U → ℝ := fun q ↦ dist ((q : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2
  have hV : IsOpen V := hA.preimage continuous_subtype_val
  have hopen : IsOpen (f '' V) :=
    (isLocalHomeomorph_planeCurveSafe_squaredRadius G hε a).isOpenMap V hV
  have hmem : dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2 ∈ f '' V := ⟨⟨p, hpU⟩, hp, rfl⟩
  have hsub : f '' V ⊆
      (fun q : PachDeZeeuw.Algebraic.Point2 ↦ dist q a ^ 2) '' (Subtype.val '' A) := by
    rintro r ⟨q, hq, rfl⟩
    exact ⟨((q : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2),
      ⟨q, hq, rfl⟩, rfl⟩
  exact interior_mono hsub (hopen.interior_eq.symm ▸ hmem)


theorem exists_planeCurveArc_equalRadius_boundary_or_critical_witness
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (o a b : PachDeZeeuw.Algebraic.Point2)
    (A B : Set (planeCurveRegularLocus G)) (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hAsafe : A ⊆ planeCurveSafeSet G ε o) (hBsafe : B ⊆ planeCurveSafeSet G ε o)
    (hne : ∃ p ∈ A, ∃ q ∈ B, dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2 = dist (q : PachDeZeeuw.Algebraic.Point2) b ^ 2) :
    ∃ p ∈ closure A, ∃ q ∈ closure B,
      dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2 = dist (q : PachDeZeeuw.Algebraic.Point2) b ^ 2 ∧
      ((p ∈ frontier A ∨ (p : PachDeZeeuw.Algebraic.Point2) ∈ planeRadialCriticalZeroSet G a) ∨
        (q ∈ frontier B ∨ (q : PachDeZeeuw.Algebraic.Point2) ∈ planeRadialCriticalZeroSet G b)) := by
  have hambient : ∃ p ∈ (Subtype.val '' A : Set PachDeZeeuw.Algebraic.Point2),
      ∃ q ∈ (Subtype.val '' B : Set PachDeZeeuw.Algebraic.Point2), dist p a ^ 2 = dist q b ^ 2 := by
    obtain ⟨p, hp, q, hq, heq⟩ := hne
    exact ⟨p, ⟨p, hp, rfl⟩, q, ⟨q, hq, rfl⟩, heq⟩
  obtain ⟨p, hp, q, hq, heq, hbad⟩ :=
    exists_equalSqDistance_boundary_or_critical_witness a b
      (Subtype.val '' A) (Subtype.val '' B)
      (planeRadialCriticalZeroSet G a) (planeRadialCriticalZeroSet G b) hambient
      (by
        rintro _ ⟨p, hp, rfl⟩ hcritical
        exact planeCurveRegular_radius_mem_interior_image G a hAopen hp hcritical)
      (by
        rintro _ ⟨q, hq, rfl⟩ hcritical
        exact planeCurveRegular_radius_mem_interior_image G b hBopen hq hcritical)
  let p' : planeCurveRegularLocus G :=
    ⟨p, mem_planeCurveRegularLocus_of_mem_closure_safe_image G hε o hAsafe hp⟩
  let q' : planeCurveRegularLocus G :=
    ⟨q, mem_planeCurveRegularLocus_of_mem_closure_safe_image G hε o hBsafe hq⟩
  have hp' : p' ∈ closure A := by
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hp
  have hq' : q' ∈ closure B := by
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hq
  refine ⟨p', hp', q', hq', heq, ?_⟩
  rcases hbad with (hpboundary | hpcritical) | (hqboundary | hqcritical)
  · apply Or.inl
    apply Or.inl
    rw [hAopen.frontier_eq]
    exact ⟨hp', fun h ↦ hpboundary.2 ⟨p', h, rfl⟩⟩
  · exact Or.inl (Or.inr hpcritical)
  · apply Or.inr
    apply Or.inl
    rw [hBopen.frontier_eq]
    exact ⟨hq', fun h ↦ hqboundary.2 ⟨q', h, rfl⟩⟩
  · exact Or.inr (Or.inr hqcritical)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem isLocalHomeomorph_connectedComponentIn_restrict
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (f : X → ℝ)
    (hf : IsLocalHomeomorph (fun y : U ↦ f y)) (x : X) :
    IsLocalHomeomorph (fun y : connectedComponentIn U x ↦ f y) := by
  have hC : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  have hinclusion : IsOpenEmbedding (Set.inclusion (connectedComponentIn_subset U x)) :=
    .inclusion _ (hC.preimage continuous_subtype_val)
  exact hf.comp hinclusion.isLocalHomeomorph


theorem exists_connectedComponentIn_restricted_real_chart
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (f : X → ℝ)
    (hf : IsLocalHomeomorph (fun y : U ↦ f y)) {x : X} (hx : x ∈ U) :
    ∃ e : (connectedComponentIn U x) ≃ₜ Set.range (fun y : connectedComponentIn U x ↦ f y),
      (∀ y, (e y : ℝ) = f y) ∧
      IsOpen (Set.range (fun y : connectedComponentIn U x ↦ f y)) ∧
      OrdConnected (Set.range (fun y : connectedComponentIn U x ↦ f y)) := by
  have hconn : IsConnected (connectedComponentIn U x) :=
    isConnected_connectedComponentIn_iff.mpr hx
  let : ConnectedSpace (connectedComponentIn U x) := isConnected_iff_connectedSpace.mp hconn
  have hg := isLocalHomeomorph_connectedComponentIn_restrict hU f hf x
  exact ⟨homeomorphRangeOfIsLocalHomeomorphReal hg,
    fun y ↦ homeomorphRangeOfIsLocalHomeomorphReal_apply_coe hg y,
    isOpen_ordConnected_range_of_isLocalHomeomorph_real hg⟩

 
theorem exists_planeCurveSafe_component_radius_chart
    (G : PlanePoly) {ε : ℝ} (hε : 0 < ε) (a : PachDeZeeuw.Algebraic.Point2)
    {x : planeCurveRegularLocus G} (hx : x ∈ planeCurveSafeSet G ε a) :
    ∃ e : (connectedComponentIn (planeCurveSafeSet G ε a) x) ≃ₜ
        Set.range (fun y : connectedComponentIn (planeCurveSafeSet G ε a) x ↦
          dist ((y : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2),
      (∀ y, (e y : ℝ) = dist ((y : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2) ∧
      IsOpen (Set.range (fun y : connectedComponentIn (planeCurveSafeSet G ε a) x ↦
        dist ((y : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2)) ∧
      OrdConnected (Set.range (fun y : connectedComponentIn (planeCurveSafeSet G ε a) x ↦
        dist ((y : planeCurveRegularLocus G) : PachDeZeeuw.Algebraic.Point2) a ^ 2)) := by
  let : LocallyConnectedSpace (planeCurveRegularLocus G) :=
    locallyConnectedSpace_planeCurveRegularLocus G
  exact exists_connectedComponentIn_restricted_real_chart
    (isOpen_planeCurveSafeSet G ε a) (fun p ↦ dist (p : PachDeZeeuw.Algebraic.Point2) a ^ 2)
    (isLocalHomeomorph_planeCurveSafe_squaredRadius G hε a) hx

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology MvPolynomial
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

private theorem inline_Esgk_PlaneCurveSafeComponentCount__planeCurveSafeBoundary_subset_zeroSet_union
    (G : PlanePoly) (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2) :
    (Subtype.val '' (planeCurveSafeBoundary G ε a)) ⊆
      planeGradientCutoffZeroSet G ε ∪ planeRadialCriticalZeroSet G a := by
  rintro p ⟨q, hq, rfl⟩
  change MvPolynomial.eval (fun i ↦ (q : PachDeZeeuw.Algebraic.Point2) i) (planeGradientSquare G) = ε ∨
    (q : PachDeZeeuw.Algebraic.Point2) ∈ PlaneCurveZeroSet (planeRadialCritical G a) at hq
  rcases hq with hcut | hcritical
  · left
    rw [planeGradientCutoffZeroSet]
    refine ⟨q.property.1, ?_⟩
    simp [PlaneCurveZeroSet, planeGradientCutoff, hcut]
  · right
    exact ⟨q.property.1, hcritical⟩


theorem planeCurveSafeBoundary_finite_and_ncard_le
    {G : PlanePoly} {d : ℕ} (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (hcutfin : (planeGradientCutoffZeroSet G ε).Finite)
    (hcutcard : (planeGradientCutoffZeroSet G ε).ncard ≤ 2 * d * (d - 1))
    (hcriticalfin : (planeRadialCriticalZeroSet G a).Finite)
    (hcriticalcard : (planeRadialCriticalZeroSet G a).ncard ≤ d * d) :
    (planeCurveSafeBoundary G ε a).Finite ∧
      (planeCurveSafeBoundary G ε a).ncard ≤ 3 * d * d := by
  let B : Set (planeCurveRegularLocus G) := planeCurveSafeBoundary G ε a
  let A : Set PachDeZeeuw.Algebraic.Point2 :=
    planeGradientCutoffZeroSet G ε ∪ planeRadialCriticalZeroSet G a
  have hAfin : A.Finite := by
    exact hcutfin.union hcriticalfin
  have himage : (Subtype.val '' B).Finite := by
    apply hAfin.subset
    exact inline_Esgk_PlaneCurveSafeComponentCount__planeCurveSafeBoundary_subset_zeroSet_union G ε a
  have hBfin : B.Finite := by
    apply himage.of_finite_image
    exact Set.injOn_of_injective Subtype.val_injective
  have hBcard : B.ncard ≤ A.ncard := by
    calc
      B.ncard = (Subtype.val '' B).ncard :=
        (Set.ncard_image_of_injective B Subtype.val_injective).symm
      _ ≤ A.ncard := Set.ncard_le_ncard
        (inline_Esgk_PlaneCurveSafeComponentCount__planeCurveSafeBoundary_subset_zeroSet_union G ε a) hAfin
  have hAcard : A.ncard ≤
      (planeGradientCutoffZeroSet G ε).ncard +
        (planeRadialCriticalZeroSet G a).ncard := by
    exact Set.ncard_union_le _ _
  have hbound : B.ncard ≤ 3 * d * d := by
    calc
      B.ncard ≤
          (planeGradientCutoffZeroSet G ε).ncard +
            (planeRadialCriticalZeroSet G a).ncard := hBcard.trans hAcard
      _ ≤ 2 * d * (d - 1) + d * d :=
        Nat.add_le_add hcutcard hcriticalcard
      _ ≤ 3 * d * d := by
        have hsub : d - 1 ≤ d := Nat.sub_le _ _
        have hcut' : 2 * d * (d - 1) ≤ 2 * d * d :=
          Nat.mul_le_mul_left (2 * d) hsub
        calc
          2 * d * (d - 1) + d * d ≤ 2 * d * d + d * d :=
            Nat.add_le_add_right hcut' _
          _ = 3 * d * d := by ring
  exact ⟨hBfin, hbound⟩


theorem planeCurveSafeComponent_finite_and_ncard_le
    {G : PlanePoly} {d : ℕ} (ε : ℝ) (a : PachDeZeeuw.Algebraic.Point2)
    (hcutfin : (planeGradientCutoffZeroSet G ε).Finite)
    (hcutcard : (planeGradientCutoffZeroSet G ε).ncard ≤ 2 * d * (d - 1))
    (hcriticalfin : (planeRadialCriticalZeroSet G a).Finite)
    (hcriticalcard : (planeRadialCriticalZeroSet G a).ncard ≤ d * d)
    (hboundary : ∀ x ∈ planeCurveSafeSet G ε a,
      ∃ b ∈ planeCurveSafeBoundary G ε a,
        b ∈ closure (connectedComponentIn (planeCurveSafeSet G ε a) x)) :
    {C : Set (planeCurveRegularLocus G) |
      ∃ x ∈ planeCurveSafeSet G ε a,
        C = connectedComponentIn (planeCurveSafeSet G ε a) x}.Finite ∧
      {C : Set (planeCurveRegularLocus G) |
        ∃ x ∈ planeCurveSafeSet G ε a,
          C = connectedComponentIn (planeCurveSafeSet G ε a) x}.ncard ≤
        6 * d * d := by
  let Bfin := planeCurveSafeBoundary_finite_and_ncard_le ε a
    hcutfin hcutcard hcriticalfin hcriticalcard
  let B : Finset (planeCurveRegularLocus G) := Bfin.1.toFinset
  have hBset : (B : Set (planeCurveRegularLocus G)) =
      planeCurveSafeBoundary G ε a := Bfin.1.coe_toFinset
  have hcount := connectedComponentIn_finite_and_ncard_le_of_finite_boundary
    (planeCurveSafeSet G ε a) B
    (isOpen_planeCurveSafeSet G ε a)
    (by simpa [hBset] using
      disjoint_planeCurveSafeSet_boundary G ε a)
    (by simpa [hBset] using
      frontier_planeCurveSafeSet_subset_boundary G ε a)
    (by
      intro x hx
      obtain ⟨b, hb, hbc⟩ := hboundary x hx
      exact ⟨b, Bfin.1.mem_toFinset.mpr hb, hbc⟩)
    (by
      intro b hb
      obtain ⟨i, e, he, _⟩ := exists_planeCurveRegular_chart G b
      exact ⟨e, he⟩)
  have hBcard : B.card ≤ 3 * d * d := by
    rw [← Set.ncard_eq_toFinset_card _ Bfin.1]
    exact Bfin.2
  have hscaled : 2 * B.card ≤ 6 * d * d := by
    calc
      2 * B.card ≤ 2 * (3 * d * d) := Nat.mul_le_mul_left 2 hBcard
      _ = 6 * d * d := by ring
  refine ⟨hcount.1, ?_⟩
  exact hcount.2.trans hscaled


end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set MvPolynomial
open scoped Classical
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


@[simp]
theorem mem_planeCurveSafeSample (G : PlanePoly) (o : PachDeZeeuw.Algebraic.Point2) (S : Finset PachDeZeeuw.Algebraic.Point2)
    {p : planeCurveRegularLocus G} :
    p ∈ planeCurveSafeSample G o S ↔
      (p : PachDeZeeuw.Algebraic.Point2) ∈ S ∧ (p : PachDeZeeuw.Algebraic.Point2) ∉ planeCurveExceptionalSample G o S := by
  simp only [planeCurveSafeSample, Finset.mem_preimage, Finset.mem_sdiff]

 
theorem planeCurveSafeSample_card_le (G : PlanePoly) (o : PachDeZeeuw.Algebraic.Point2) (S : Finset PachDeZeeuw.Algebraic.Point2) :
    (planeCurveSafeSample G o S).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn Subtype.val
    (fun p hp ↦ ((mem_planeCurveSafeSample G o S).mp hp).1)
  exact Subtype.val_injective.injOn


theorem not_mem_planeCurveExceptionalSample_of_mem_safe
    {G : PlanePoly} {ε : ℝ} {o : PachDeZeeuw.Algebraic.Point2} (S : Finset PachDeZeeuw.Algebraic.Point2)
    {p : planeCurveRegularLocus G} (hp : p ∈ planeCurveSafeSet G ε o) :
    (p : PachDeZeeuw.Algebraic.Point2) ∉ planeCurveExceptionalSample G o S := by
  intro he
  rcases (Finset.mem_filter.mp he).2 with hsingular | hcritical
  · exact p.property.2 hsingular
  · exact hp.2 hcritical.2


theorem planeCurveSafeSample_subset_safe (G : PlanePoly) {ε : ℝ} (o : PachDeZeeuw.Algebraic.Point2)
    (S : Finset PachDeZeeuw.Algebraic.Point2)
    (hbelow : ∀ p ∈ S, p ∉ SingularPointSet G →
      ε < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G)) :
    (planeCurveSafeSample G o S : Set (planeCurveRegularLocus G)) ⊆
      planeCurveSafeSet G ε o := by
  intro p hp
  obtain ⟨hpS, hkeep⟩ := (mem_planeCurveSafeSample G o S).mp hp
  refine ⟨hbelow p hpS p.property.2, ?_⟩
  intro hcritical
  exact hkeep (Finset.mem_filter.mpr ⟨hpS, Or.inr ⟨p.property.1, hcritical⟩⟩)

 
theorem exists_mem_planeCurveSafeSample_of_not_exceptional
    {G : PlanePoly} {o : PachDeZeeuw.Algebraic.Point2} {S : Finset PachDeZeeuw.Algebraic.Point2}
    (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G)
    {p : PachDeZeeuw.Algebraic.Point2} (hp : p ∈ S) (hkeep : p ∉ planeCurveExceptionalSample G o S) :
    ∃ q : planeCurveRegularLocus G, q ∈ planeCurveSafeSample G o S ∧ (q : PachDeZeeuw.Algebraic.Point2) = p := by
  have hregular : p ∈ planeCurveRegularLocus G := by
    refine ⟨hS p hp, ?_⟩
    intro hsingular
    exact hkeep (Finset.mem_filter.mpr ⟨hp, Or.inl hsingular⟩)
  refine ⟨⟨p, hregular⟩, ?_, rfl⟩
  exact (mem_planeCurveSafeSample G o S).mpr ⟨hp, hkeep⟩


theorem planeCurveSafeSample_filter_card_le
    (G : PlanePoly) {ε : ℝ} (o : PachDeZeeuw.Algebraic.Point2) (S T : Finset PachDeZeeuw.Algebraic.Point2) (hTS : T ⊆ S)
    {A : Set (planeCurveRegularLocus G)} (hA : A ⊆ planeCurveSafeSet G ε o) :
    (T.filter (fun q ↦ q ∈ Subtype.val '' A)).card ≤
      ((planeCurveSafeSample G o S).filter (fun p ↦ p ∈ A)).card := by
  let P := (planeCurveSafeSample G o S).filter (fun p ↦ p ∈ A)
  have hsubset : T.filter (fun q ↦ q ∈ Subtype.val '' A) ⊆ P.image Subtype.val := by
    intro q hq
    obtain ⟨hqT, p, hpA, rfl⟩ := Finset.mem_filter.mp hq
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨?_, hpA⟩, rfl⟩
    exact (mem_planeCurveSafeSample G o S).mpr
      ⟨hTS hqT, not_mem_planeCurveExceptionalSample_of_mem_safe S (hA hpA)⟩
  calc
    (T.filter (fun q ↦ q ∈ Subtype.val '' A)).card ≤ (P.image Subtype.val).card :=
      Finset.card_le_card hsubset
    _ = P.card := Finset.card_image_of_injective P Subtype.val_injective


theorem planeCurveSafeSample_subtype_filter_card_le
    (G : PlanePoly) {ε : ℝ} (o : PachDeZeeuw.Algebraic.Point2) (S T : Finset PachDeZeeuw.Algebraic.Point2) (hTS : T ⊆ S)
    {A : Set (planeCurveRegularLocus G)} (hA : A ⊆ planeCurveSafeSet G ε o) :
    ((Finset.univ : Finset T).filter (fun q : T ↦ (q : PachDeZeeuw.Algebraic.Point2) ∈ Subtype.val '' A)).card ≤
      ((planeCurveSafeSample G o S).filter (fun p ↦ p ∈ A)).card := by
  have hcard :
      ((Finset.univ : Finset T).filter (fun q : T ↦ (q : PachDeZeeuw.Algebraic.Point2) ∈ Subtype.val '' A)).card ≤
        (T.filter (fun q ↦ q ∈ Subtype.val '' A)).card := by
    apply Finset.card_le_card_of_injOn (Subtype.val : T → PachDeZeeuw.Algebraic.Point2)
    · intro q hq
      exact Finset.mem_filter.mpr ⟨q.property, (Finset.mem_filter.mp hq).2⟩
    · exact Subtype.val_injective.injOn
  exact hcard.trans (planeCurveSafeSample_filter_card_le G o S T hTS hA)

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


noncomputable section

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)
open PachDeZeeuw.Algebraic (PlanePoly PlaneCurveZeroSet)


theorem maximallyCircularRestrictedRawAuxiliaryIncidence_of_intrinsicCellCover
    (hcover : MaximallyCircularIntrinsicCellCoverStatement) :
    MaximallyCircularRestrictedRawAuxiliaryIncidenceStatement := by
  classical
  refine ⟨256, by norm_num, ?_⟩
  intro G S X hG habs hnotcircle hmax hS hself hcarrier hdisj hpart hbal₁ hbal₂ hpos j hj hsmall
  obtain ⟨grid⟩ := hcover G S X hG habs hnotcircle hmax hS hself hcarrier
    hdisj hpart hbal₁ hbal₂ hpos j hj hsmall
  have hd : 2 ≤ G.totalDegree := hmax.two_le_totalDegree_of_irreducible hG
  have hdpos : 0 < (G.totalDegree : ℝ) := by exact_mod_cast (by omega : 0 < G.totalDegree)
  have hjpos : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hN : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have hp₁ : X.P₁.card ≤ S.card := Finset.card_le_card (by
    rw [← hpart]
    exact Finset.subset_union_left)
  have hp₂ : X.P₂.card ≤ S.card := Finset.card_le_card (by
    rw [← hpart]
    exact Finset.subset_union_right)
  obtain ⟨Δ, hΔ, hcells⟩ := maximallyCircularCellIncidence_of_external
    (ι := ℕ) X hself hd hG hmax hnotcircle hcarrier
  let bad := grid.exceptional ∪ Δ
  let P : ℕ → Finset (X.P₂ × X.P₂) := fun ω ↦ grid.points ω \ Δ
  have hbad : bad.card ≤ 12 * G.totalDegree ^ 2 * S.card := by
    calc
      bad.card ≤ grid.exceptional.card + Δ.card := Finset.card_union_le _ _
      _ ≤ 4 * G.totalDegree ^ 2 * S.card +
          8 * G.totalDegree ^ 2 * X.P₂.card :=
        Nat.add_le_add grid.exceptional_card_le hΔ
      _ ≤ 4 * G.totalDegree ^ 2 * S.card +
          8 * G.totalDegree ^ 2 * S.card :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hp₂) _
      _ = 12 * G.totalDegree ^ 2 * S.card := by ring
  have hloss : bad.card * (2 * G.totalDegree * X.P₁.card) ≤
      24 * G.totalDegree ^ 3 * S.card ^ 2 := by
    calc
      bad.card * (2 * G.totalDegree * X.P₁.card) ≤
          (12 * G.totalDegree ^ 2 * S.card) * (2 * G.totalDegree * S.card) :=
        Nat.mul_le_mul hbad (Nat.mul_le_mul_left _ hp₁)
      _ = 24 * G.totalDegree ^ 3 * S.card ^ 2 := by ring
  have hfinite := finiteIncidenceCount_le_of_cover
    (Finset.univ : Finset (X.P₂ × X.P₂))
    (Finset.univ : Finset (X.P₁ × X.P₁))
    (auxPointPairCurveIncidence X) bad grid.cells P grid.labels
    (2 * G.totalDegree * X.P₁.card)
    (by
      intro pq _
      by_cases hb : pq ∈ bad
      · exact Or.inl hb
      · have hex : pq ∉ grid.exceptional := fun h ↦ hb (Finset.mem_union_left _ h)
        have hdel : pq ∉ Δ := fun h ↦ hb (Finset.mem_union_right _ h)
        obtain ⟨ω, hω, hpω⟩ := grid.covers pq hex
        exact Or.inr ⟨ω, hω, Finset.mem_sdiff.mpr ⟨hpω, hdel⟩⟩)
    (by
      intro ω hω pq hpq ij _ hinc
      exact grid.labels_cover ω hω pq (Finset.mem_sdiff.mp hpq).1 ij hinc)
    (by
      intro pq _
      exact auxPointPairCurveIncidence_label_card_le X hself pq)
  have hdisjoint : ∀ ω ∈ grid.cells, Disjoint (P ω) Δ := by
    intro ω _
    exact Finset.disjoint_left.mpr fun _ hp hδ ↦ (Finset.mem_sdiff.mp hp).2 hδ
  have hpoints : ∀ ω ∈ grid.cells, ((P ω).card : ℝ) ≤
      4 * (S.card : ℝ) ^ 2 / ((G.totalDegree : ℝ) ^ 2 * (j : ℝ) ^ 2) := by
    intro ω hω
    exact le_trans (by exact_mod_cast (Finset.card_le_card (Finset.sdiff_subset) :
      (P ω).card ≤ (grid.points ω).card)) (grid.points_card_le ω hω)
  have hcellbound := hcells grid.cells P grid.labels
    (4 * (S.card : ℝ) ^ 2 / ((G.totalDegree : ℝ) ^ 2 * (j : ℝ) ^ 2))
    (2 * (G.totalDegree : ℝ) ^ 2 * (j : ℝ) ^ 2)
    (20 * (G.totalDegree : ℝ) ^ 2 * (j : ℝ) * (S.card : ℝ) ^ 2)
    hdisjoint (by positivity) grid.cells_card_le grid.labels_card_le hpoints
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hcellbound
  have hsqrt := intrinsicCellIncidence_sqrt_product_le
    (G.totalDegree : ℝ) (j : ℝ) (S.card : ℝ) hdpos hjpos hN
  have hsum := intrinsicCellIncidence_scale_sum_le
    (G.totalDegree : ℝ) (j : ℝ) (S.card : ℝ) hdpos hjpos hN
  have hfiniteReal : (finiteIncidenceCount
      (Finset.univ : Finset (X.P₂ × X.P₂))
      (Finset.univ : Finset (X.P₁ × X.P₁))
      (auxPointPairCurveIncidence X) : ℝ) ≤
      (bad.card * (2 * G.totalDegree * X.P₁.card) : ℕ) +
        ∑ ω ∈ grid.cells,
          (finiteIncidenceCount (P ω) (grid.labels ω)
            (auxPointPairCurveIncidence X) : ℝ) := by exact_mod_cast hfinite
  have hlossReal : (bad.card * (2 * G.totalDegree * X.P₁.card) : ℕ) ≤
      (24 : ℝ) * (G.totalDegree : ℝ) ^ 3 * (S.card : ℝ) ^ 2 := by
    exact_mod_cast hloss
  norm_num only [Nat.cast_ofNat]
  linarith

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open scoped Classical
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem nonempty_planeCurveArcPartition
    {G : PlanePoly} {d : ℕ} {ε : ℝ} (hε : 0 < ε) (o : PachDeZeeuw.Algebraic.Point2)
    (hcutfin : (planeGradientCutoffZeroSet G ε).Finite)
    (hcutcard : (planeGradientCutoffZeroSet G ε).ncard ≤ 2 * d * (d - 1))
    (hcriticalfin : (planeRadialCriticalZeroSet G o).Finite)
    (hcriticalcard : (planeRadialCriticalZeroSet G o).ncard ≤ d * d)
    (P : Finset (planeCurveRegularLocus G))
    (hPU : (P : Set (planeCurveRegularLocus G)) ⊆ planeCurveSafeSet G ε o)
    (k : ℕ) (hk : 0 < k) :
    Nonempty (PlaneCurveArcPartition G ε o P d k) := by
  let M := planeCurveRegularLocus G
  let U : Set M := planeCurveSafeSet G ε o
  let : LocallyConnectedSpace M := locallyConnectedSpace_planeCurveRegularLocus G
  have hUopen : IsOpen U := isOpen_planeCurveSafeSet G ε o
  have hB := planeCurveSafeBoundary_finite_and_ncard_le ε o
    hcutfin hcutcard hcriticalfin hcriticalcard
  have hcomponents := planeCurveSafeComponent_finite_and_ncard_le ε o
    hcutfin hcutcard hcriticalfin hcriticalcard
    (fun x hx ↦ exists_planeCurveSafe_component_boundary G hε o hx)
  let F : Finset (Set M) := hcomponents.1.toFinset
  have hFmem (C : Set M) : C ∈ F ↔ ∃ x ∈ U, C = connectedComponentIn U x :=
    hcomponents.1.mem_toFinset
  have hFcard : F.card ≤ 6 * d * d := by
    change hcomponents.1.toFinset.card ≤ _
    rw [← Set.ncard_eq_toFinset_card _ hcomponents.1]
    exact hcomponents.2
  have hFopen : ∀ C ∈ F, IsOpen C := by
    intro C hC
    obtain ⟨x, _, rfl⟩ := (hFmem C).mp hC
    exact hUopen.connectedComponentIn
  have hFdisj : (F : Set (Set M)).Pairwise Disjoint := by
    intro C hC D hD hne
    obtain ⟨x, _, rfl⟩ := (hFmem C).mp hC
    obtain ⟨y, _, rfl⟩ := (hFmem D).mp hD
    apply Set.disjoint_left.mpr
    intro p hpC hpD
    exact hne ((connectedComponentIn_eq hpC).trans (connectedComponentIn_eq hpD).symm)
  have hFcover : (⋃ C ∈ F, C) = U := by
    ext p
    constructor
    · intro hp
      obtain ⟨C, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hC, hp⟩ := Set.mem_iUnion.mp hp
      obtain ⟨x, _, rfl⟩ := (hFmem C).mp hC
      exact connectedComponentIn_subset U x hp
    · intro hp
      exact Set.mem_iUnion.mpr ⟨connectedComponentIn U p,
        Set.mem_iUnion.mpr ⟨(hFmem _).mpr ⟨p, hp, rfl⟩, mem_connectedComponentIn hp⟩⟩
  let f : M → ℝ := fun p ↦ dist (p : PachDeZeeuw.Algebraic.Point2) o ^ 2
  have hf : Continuous f := (continuous_subtype_val.dist continuous_const).pow 2
  have hcharts : ∀ C ∈ F, ∃ J : Set ℝ, IsOpen J ∧ J.OrdConnected ∧
      ∃ e : C ≃ₜ J, ∀ p : C, (e p : ℝ) = f p := by
    intro C hC
    obtain ⟨x, hx, rfl⟩ := (hFmem C).mp hC
    obtain ⟨e, he, hJopen, hJord⟩ := exists_planeCurveSafe_component_radius_chart G hε o hx
    exact ⟨_, hJopen, hJord, e, he⟩
  obtain ⟨K, A, hKU, hPK, hKcard, hAcard, hAprops, hApair, hAcover⟩ :=
    exists_finite_chart_partition_aggregation U F hFopen hFdisj hFcover
      f hf hcharts P hPU k hk
  let B : Finset M := hB.1.toFinset
  let D : Finset M := B ∪ K
  have hBcard : B.card ≤ 3 * d * d := by
    change hB.1.toFinset.card ≤ _
    rw [← Set.ncard_eq_toFinset_card _ hB.1]
    exact hB.2
  have hDcard : D.card ≤ K.card + 3 * d * d := by
    have hcard := Finset.card_union_le B K
    dsimp [D]
    omega
  have hfrontier : frontier (U \ (K : Set M)) ⊆ (D : Set M) := by
    intro p hp
    change p ∈ frontier (U ∩ (K : Set M)ᶜ) at hp
    rcases frontier_inter_subset U (K : Set M)ᶜ hp with hpU | hpK
    · apply Finset.mem_union_left
      exact hB.1.mem_toFinset.mpr (frontier_planeCurveSafeSet_subset_boundary G ε o hpU.1)
    · apply Finset.mem_union_right
      rw [frontier_compl] at hpK
      have hpclosure := frontier_subset_closure hpK.2
      simpa only [K.finite_toSet.isClosed.closure_eq, Finset.mem_coe] using hpclosure
  have hsUnion : ⋃₀ (A : Set (Set M)) = U \ (K : Set M) := by
    calc
      ⋃₀ (A : Set (Set M)) = (⋃ C ∈ A, C) := by ext p; simp
      _ = U \ (K : Set M) := hAcover
  have hAfrontier : ∀ C ∈ A, frontier C ⊆ (D : Set M) := by
    intro C hC
    have hsub := frontier_subset_frontier_sUnion_of_open_pairwise_disjoint
      (A : Set (Set M)) (fun V hV ↦ (hAprops V hV).2.1)
      (fun hV hW hne ↦ hApair hV hW hne) hC
    rw [hsUnion] at hsub
    exact hsub.trans hfrontier
  have hclosure : ∀ p : M, (A.filter (fun C ↦ p ∈ closure C)).card ≤ 2 := by
    intro p
    obtain ⟨i, e, hp, _⟩ := exists_planeCurveRegular_chart G p
    exact Finset.card_filter_closure_le_two_of_open_preconnected_pairwise_disjoint
      A (fun C hC ↦ (hAprops C hC).1) (fun C hC ↦ (hAprops C hC).2.1)
      (fun C hC ↦ (hAprops C hC).2.2.1.isPreconnected) hApair D
      (by rw [hAcover]; exact hfrontier) e hp
  exact ⟨{
    cuts := K
    arcs := A
    boundary := D
    level_pos := hε
    cuts_subset := hKU
    cuts_disjoint := hPK
    cuts_card_le := hKcard
    arcs_card_le := hAcard.trans (Nat.add_le_add_left hFcard K.card)
    boundary_card_le := hDcard
    arc_properties := hAprops
    arcs_disjoint := hApair
    arcs_cover := hAcover
    arc_frontier := hAfrontier
    closure_card_le := hclosure }⟩

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw (PreparedBipartiteInput)

theorem nonempty_intrinsicAuxiliaryCellCover_of_finite_index
    {ι : Type*} {d N j : ℕ} (X : PreparedBipartiteInput d)
    (cells : Finset ι)
    (points : ι → Finset (X.P₂ × X.P₂))
    (labels : ι → Finset (X.P₁ × X.P₁))
    (exceptional : Finset (X.P₂ × X.P₂))
    (hexceptional : exceptional.card ≤ 4 * d ^ 2 * N)
    (hcovers : ∀ pq, pq ∉ exceptional → ∃ ω ∈ cells, pq ∈ points ω)
    (hlabels : ∀ ω ∈ cells, ∀ pq ∈ points ω, ∀ ij,
      auxPointPairCurveIncidence X pq ij → ij ∈ labels ω)
    (hcells : (cells.card : ℝ) ≤ 2 * (d : ℝ) ^ 2 * (j : ℝ) ^ 2)
    (hpoints : ∀ ω ∈ cells,
      ((points ω).card : ℝ) ≤
        4 * (N : ℝ) ^ 2 / ((d : ℝ) ^ 2 * (j : ℝ) ^ 2))
    (hlabels_card : (∑ ω ∈ cells, ((labels ω).card : ℝ)) ≤
      20 * (d : ℝ) ^ 2 * (j : ℝ) * (N : ℝ) ^ 2) :
    Nonempty (IntrinsicAuxiliaryCellCover X N j) := by
  classical
  let e := cells.equivFin.symm
  let points' : ℕ → Finset (X.P₂ × X.P₂) := fun n ↦
    if h : n < cells.card then points ((e ⟨n, h⟩).1) else ∅
  let labels' : ℕ → Finset (X.P₁ × X.P₁) := fun n ↦
    if h : n < cells.card then labels ((e ⟨n, h⟩).1) else ∅
  have hpoints'_at (i : {x // x ∈ cells}) :
      points' (e.symm i).1 = points i.1 := by
    simp [points', e]
  have hpoints'_mapped (n : ℕ) (hn : n < cells.card) :
      points' n = points (e ⟨n, hn⟩).1 := by
    let i : {x // x ∈ cells} := e ⟨n, hn⟩
    simpa [i, e] using hpoints'_at i
  have hlabels'_at (i : {x // x ∈ cells}) :
      labels' (e.symm i).1 = labels i.1 := by
    simp [labels', e]
  have hlabels'_mapped (n : ℕ) (hn : n < cells.card) :
      labels' n = labels (e ⟨n, hn⟩).1 := by
    let i : {x // x ∈ cells} := e ⟨n, hn⟩
    simpa [i, e] using hlabels'_at i
  refine ⟨
    { cells := Finset.range cells.card
      points := points'
      labels := labels'
      exceptional := exceptional
      exceptional_card_le := hexceptional
      covers := ?_
      labels_cover := ?_
      cells_card_le := ?_
      points_card_le := ?_
      labels_card_le := ?_ }⟩
  · intro pq hpq
    obtain ⟨ω, hω, hpω⟩ := hcovers pq hpq
    let i : {x // x ∈ cells} := ⟨ω, hω⟩
    let n := e.symm i
    refine ⟨n.1, Finset.mem_range.mpr n.isLt, ?_⟩
    have hpi' : points' n.1 = points i.1 := by
      simpa [n] using hpoints'_at i
    rw [hpi']
    exact hpω
  · intro ω hω pq hpq ij hinc
    have hωlt : ω < cells.card := Finset.mem_range.mp hω
    let i : {x // x ∈ cells} := e ⟨ω, hωlt⟩
    have hpi : pq ∈ points i.1 := by
      rw [← hpoints'_mapped ω hωlt]
      exact hpq
    have hij := hlabels i.1 i.2 pq hpi ij hinc
    rw [hlabels'_mapped ω hωlt]
    exact hij
  · simpa using hcells
  · intro ω hω
    have hωlt : ω < cells.card := Finset.mem_range.mp hω
    let i : {x // x ∈ cells} := e ⟨ω, hωlt⟩
    rw [hpoints'_mapped ω hωlt]
    exact hpoints i.1 i.2
  · have hsum :
        (∑ ω ∈ Finset.range cells.card, ((labels' ω).card : ℝ)) =
          ∑ ω ∈ cells, ((labels ω).card : ℝ) := by
      apply Finset.sum_bij
        (fun ω hω ↦ (e ⟨ω, Finset.mem_range.mp hω⟩).1) ?_ ?_ ?_ ?_
      · intro ω hω
        exact (e ⟨ω, Finset.mem_range.mp hω⟩).2
      · intro ω₁ hω₁ ω₂ hω₂ heq
        have hi :
            e ⟨ω₁, Finset.mem_range.mp hω₁⟩ =
              e ⟨ω₂, Finset.mem_range.mp hω₂⟩ := Subtype.ext heq
        simpa only [Equiv.symm_apply_apply] using
          congrArg (fun z : {x // x ∈ cells} ↦ (e.symm z).1) hi
      · intro ω hω
        let n := e.symm ⟨ω, hω⟩
        refine ⟨n.1, Finset.mem_range.mpr n.isLt, ?_⟩
        simp [n]
      · intro ω hω
        rw [hlabels'_mapped ω (Finset.mem_range.mp hω)]
    rw [hsum]
    exact hlabels_card

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open scoped Classical
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk


theorem planeCurveArcPairVisits_card_le_of_fiber_bounds
    {G : PlanePoly} {ε : ℝ} {o : PachDeZeeuw.Algebraic.Point2}
    {P : Finset (planeCurveRegularLocus G)} {d k : ℕ}
    (H : PlaneCurveArcPartition G ε o P d k) (a b : PachDeZeeuw.Algebraic.Point2)
    (hA : ∀ r : ℝ, (planeCurveSquaredRadiusFiber G a r).Finite ∧
      (planeCurveSquaredRadiusFiber G a r).ncard ≤ 2 * d)
    (hB : ∀ r : ℝ, (planeCurveSquaredRadiusFiber G b r).Finite ∧
      (planeCurveSquaredRadiusFiber G b r).ncard ≤ 2 * d)
    (hAfin : (planeRadialCriticalZeroSet G a).Finite)
    (hAcard : (planeRadialCriticalZeroSet G a).ncard ≤ d * d)
    (hBfin : (planeRadialCriticalZeroSet G b).Finite)
    (hBcard : (planeRadialCriticalZeroSet G b).ncard ≤ d * d) :
    (planeCurveArcPairVisits H.arcs a b).card ≤
      4 * (2 * d * (2 * H.boundary.card + 2 * d * d)) := by
  let M := planeCurveRegularLocus G
  let DA : Finset PachDeZeeuw.Algebraic.Point2 := H.boundary.image Subtype.val ∪ hAfin.toFinset
  let DB : Finset PachDeZeeuw.Algebraic.Point2 := H.boundary.image Subtype.val ∪ hBfin.toFinset
  have hDA : DA.card ≤ H.boundary.card + d * d := by
    have hcrit : hAfin.toFinset.card ≤ d * d := by
      rw [← Set.ncard_eq_toFinset_card _ hAfin]
      exact hAcard
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) hcrit)
  have hDB : DB.card ≤ H.boundary.card + d * d := by
    have hcrit : hBfin.toFinset.card ≤ d * d := by
      rw [← Set.ncard_eq_toFinset_card _ hBfin]
      exact hBcard
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add (Finset.card_image_le) hcrit)
  obtain ⟨W, hWcard, hW⟩ :=
    exists_planeCurveBoundaryWitnesses_of_fiber_bounds G d a b DA DB hA hB
  let v : M × M → PachDeZeeuw.Algebraic.Point2 × PachDeZeeuw.Algebraic.Point2 := fun z ↦ (z.1.val, z.2.val)
  have hv : Function.Injective v := by
    intro x y h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (Subtype.ext (congrArg Prod.snd h))
  let R : Finset (M × M) := W.preimage v hv.injOn
  have hRcard : R.card ≤ W.card := by
    rw [Finset.card_preimage]
    exact Finset.card_filter_le _ _
  let V : M × M → Finset (Set M × Set M) := fun z ↦
    (H.arcs ×ˢ H.arcs).filter (fun C ↦ z.1 ∈ closure C.1 ∧ z.2 ∈ closure C.2)
  have hVcard (z : M × M) : (V z).card ≤ 4 :=
    Finset.card_product_filter_closure_le_four H.arcs H.arcs
      (H.closure_card_le z.1) (H.closure_card_le z.2)
  have hcover : planeCurveArcPairVisits H.arcs a b ⊆ R.biUnion V := by
    intro C hC
    obtain ⟨hC, hne⟩ := Finset.mem_filter.mp hC
    obtain ⟨hC₁, hC₂⟩ := Finset.mem_product.mp hC
    have hprops₁ := H.arc_properties C.1 hC₁
    have hprops₂ := H.arc_properties C.2 hC₂
    obtain ⟨p, hp, q, hq, heq, hbad⟩ :=
      exists_planeCurveArc_equalRadius_boundary_or_critical_witness
        G H.level_pos o a b C.1 C.2 hprops₁.2.1 hprops₂.2.1
        hprops₁.2.2.2.1 hprops₂.2.2.2.1 hne
    have hdistinguished : (p : PachDeZeeuw.Algebraic.Point2) ∈ DA ∨ (q : PachDeZeeuw.Algebraic.Point2) ∈ DB := by
      rcases hbad with (hpB | hpcrit) | (hqB | hqcrit)
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨p, H.arc_frontier C.1 hC₁ hpB, rfl⟩))
      · exact Or.inl (Finset.mem_union_right _ (hAfin.mem_toFinset.mpr hpcrit))
      · exact Or.inr (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨q, H.arc_frontier C.2 hC₂ hqB, rfl⟩))
      · exact Or.inr (Finset.mem_union_right _ (hBfin.mem_toFinset.mpr hqcrit))
    apply Finset.mem_biUnion.mpr
    refine ⟨(p, q), ?_, ?_⟩
    · exact Finset.mem_preimage.mpr
        (hW p p.property.1 q q.property.1 heq hdistinguished)
    · exact Finset.mem_filter.mpr ⟨hC, hp, hq⟩
  calc
    (planeCurveArcPairVisits H.arcs a b).card ≤ (R.biUnion V).card :=
      Finset.card_le_card hcover
    _ ≤ R.card * 4 := Finset.card_biUnion_le_card_mul R V 4 (fun z _ ↦ hVcard z)
    _ ≤ W.card * 4 := Nat.mul_le_mul_right _ hRcard
    _ ≤ (2 * d * (DA.card + DB.card)) * 4 := Nat.mul_le_mul_right _ hWcard
    _ ≤ (2 * d * (2 * H.boundary.card + 2 * d * d)) * 4 := by
      apply Nat.mul_le_mul_right
      apply Nat.mul_le_mul_left
      nlinarith only [hDA, hDB]
    _ = 4 * (2 * d * (2 * H.boundary.card + 2 * d * d)) := by ring


theorem planeCurveArcPairVisits_card_le_of_sample
    {G : PlanePoly} {ε : ℝ} {o : PachDeZeeuw.Algebraic.Point2}
    {P : Finset (planeCurveRegularLocus G)} {d k : ℕ}
    (H : PlaneCurveArcPartition G ε o P d k)
    (hG : Irreducible G) (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G) (hsize : 2 ≤ S.card)
    (a b : PachDeZeeuw.Algebraic.Point2)
    (hAfin : (planeRadialCriticalZeroSet G a).Finite)
    (hAcard : (planeRadialCriticalZeroSet G a).ncard ≤ d * d)
    (hBfin : (planeRadialCriticalZeroSet G b).Finite)
    (hBcard : (planeRadialCriticalZeroSet G b).ncard ≤ d * d) :
    (planeCurveArcPairVisits H.arcs a b).card ≤
      4 * (2 * d * (2 * H.boundary.card + 2 * d * d)) :=
  planeCurveArcPairVisits_card_le_of_fiber_bounds H a b
    (fun r ↦ planeCurveSquaredRadiusFiber_finite_and_ncard_le_of_sample
      hG hdegree hmax hnot S hS hsize a r)
    (fun r ↦ planeCurveSquaredRadiusFiber_finite_and_ncard_le_of_sample
      hG hdegree hmax hnot S hS hsize b r)
    hAfin hAcard hBfin hBcard

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

open Set Topology
open scoped Classical
open PachDeZeeuw (PreparedBipartiteInput auxCurve)
open PachDeZeeuw.Algebraic hiding Point2

namespace Esgk

 
private theorem inline_Esgk_PlaneCurveIntrinsicCellCover__intrinsicCover_incidence_sqRadius {d : ℕ}
    (X : PreparedBipartiteInput d) (pq : X.P₂ × X.P₂) (ij : X.P₁ × X.P₁)
    (hinc : auxPointPairCurveIncidence X pq ij) :
    dist (pq.1 : PachDeZeeuw.Algebraic.Point2) (ij.1 : PachDeZeeuw.Algebraic.Point2) ^ 2 =
      dist (pq.2 : PachDeZeeuw.Algebraic.Point2) (ij.2 : PachDeZeeuw.Algebraic.Point2) ^ 2 := by
  have hcurve : encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)) ∈
      auxCurve X ij.1 ij.2 := hinc
  have hsq := hcurve.2.2
  change dist (ij.1 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxFirst (encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 =
    dist (ij.2 : PachDeZeeuw.Algebraic.Point2)
      (decodedAuxSecond (encodedAuxPoint ((pq.1 : PachDeZeeuw.Algebraic.Point2), (pq.2 : PachDeZeeuw.Algebraic.Point2)))) ^ 2 at hsq
  simpa [dist_comm] using hsq


theorem nonempty_intrinsicAuxiliaryCellCover_of_arcPartition
    {G : PlanePoly} {d j : ℕ} {ε : ℝ} (o : PachDeZeeuw.Algebraic.Point2)
    (S : Finset PachDeZeeuw.Algebraic.Point2) (X : PreparedBipartiteInput d)
    (hG : Irreducible G) (hdegree : G.totalDegree ≤ d)
    (hmax : IsMaximallyCircular G) (hnot : ¬ IsCircleFactor G)
    (hS : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G)
    (hsize : 2 ≤ S.card) (hP₁ : X.P₁ ⊆ S) (hP₂ : X.P₂ ⊆ S)
    (hd : 0 < d) (hj : 24 * d ≤ j) (hN : j * d < S.card)
    (hbelow : ∀ p ∈ S, p ∉ SingularPointSet G →
      ε < MvPolynomial.eval (fun i ↦ p i) (planeGradientSquare G))
    (hcritical : ∀ a : PachDeZeeuw.Algebraic.Point2, (planeRadialCriticalZeroSet G a).Finite ∧
      (planeRadialCriticalZeroSet G a).ncard ≤ d * d)
    (H : PlaneCurveArcPartition G ε o (planeCurveSafeSample G o S) d
      (intrinsicPartitionBlockSize d j S.card)) :
    Nonempty (IntrinsicAuxiliaryCellCover X S.card j) := by
  let M := planeCurveRegularLocus G
  let k := intrinsicPartitionBlockSize d j S.card
  let P := planeCurveSafeSample G o S
  let excluded := planeCurveExceptionalSample G o S
  let bad : Finset X.P₂ := Finset.univ.filter (fun q : X.P₂ ↦ (q : PachDeZeeuw.Algebraic.Point2) ∈ excluded)
  let exceptional : Finset (X.P₂ × X.P₂) :=
    (bad ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ bad)
  have hE : excluded.card ≤ 2 * d ^ 2 :=
    planeCurveExceptionalSample_card_le hG hdegree o S (hcritical o).1 (hcritical o).2
  have hbad : bad.card ≤ 2 * d ^ 2 := by
    apply le_trans (Finset.card_le_card_of_injOn (fun q : X.P₂ ↦ (q : PachDeZeeuw.Algebraic.Point2)) ?_ ?_) hE
    · intro q hq
      exact (Finset.mem_filter.mp hq).2
    · intro p hp q hq heq
      exact Subtype.ext heq
  have hexceptional : exceptional.card ≤ 4 * d ^ 2 * S.card := by
    have hbase := exceptional_ordered_pairs_card_le (Finset.univ : Finset X.P₂) bad hbad
    have htarget : (Finset.univ : Finset X.P₂).card ≤ S.card := by
      simpa using Finset.card_le_card hP₂
    exact hbase.trans (Nat.mul_le_mul_left _ htarget)
  let cells := H.arcs ×ˢ H.arcs
  let targets : Set M → Finset X.P₂ := fun A ↦
    Finset.univ.filter (fun q : X.P₂ ↦ (q : PachDeZeeuw.Algebraic.Point2) ∈ Subtype.val '' A)
  let points : Set M × Set M → Finset (X.P₂ × X.P₂) := fun C ↦
    targets C.1 ×ˢ targets C.2
  let labels : Set M × Set M → Finset (X.P₁ × X.P₁) := fun C ↦
    Finset.univ.filter (fun ij ↦ C ∈ planeCurveArcPairVisits H.arcs ij.1 ij.2)
  have hretained (q : X.P₂) (hq : q ∉ bad) :
      ∃ A ∈ H.arcs, (q : PachDeZeeuw.Algebraic.Point2) ∈ Subtype.val '' A := by
    have hkeep : (q : PachDeZeeuw.Algebraic.Point2) ∉ excluded := by
      intro he
      exact hq (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
    obtain ⟨q', hq'P, hq'q⟩ :=
      exists_mem_planeCurveSafeSample_of_not_exceptional hS (hP₂ q.property) hkeep
    have hq'U : q' ∈ planeCurveSafeSet G ε o :=
      planeCurveSafeSample_subset_safe G o S hbelow hq'P
    have hq'K : q' ∉ H.cuts := by
      intro hcut
      exact Finset.disjoint_left.mp H.cuts_disjoint hq'P hcut
    have hq'cover : q' ∈ ⋃ A ∈ H.arcs, A := by
      rw [H.arcs_cover]
      exact ⟨hq'U, hq'K⟩
    obtain ⟨A, hq'A⟩ := Set.mem_iUnion.mp hq'cover
    obtain ⟨hA, hq'A⟩ := Set.mem_iUnion.mp hq'A
    exact ⟨A, hA, q', hq'A, hq'q⟩
  have hcovers : ∀ pq, pq ∉ exceptional → ∃ C ∈ cells, pq ∈ points C := by
    intro pq hpq
    have hp : pq.1 ∉ bad := by
      intro hp
      exact hpq (Finset.mem_union_left _
        (Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩))
    have hq : pq.2 ∉ bad := by
      intro hq
      exact hpq (Finset.mem_union_right _
        (Finset.mem_product.mpr ⟨Finset.mem_univ _, hq⟩))
    obtain ⟨A, hA, hpA⟩ := hretained pq.1 hp
    obtain ⟨B, hB, hqB⟩ := hretained pq.2 hq
    exact ⟨(A, B), Finset.mem_product.mpr ⟨hA, hB⟩,
      Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpA⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqB⟩⟩⟩
  have hlabels : ∀ C ∈ cells, ∀ pq ∈ points C, ∀ ij,
      auxPointPairCurveIncidence X pq ij → ij ∈ labels C := by
    intro C hC pq hpq ij hinc
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    obtain ⟨p, hpA, hpval⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨q, hqA, hqval⟩ := (Finset.mem_filter.mp hq).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨hC, p, hpA, q, hqA, ?_⟩
    simpa only [hpval, hqval] using inline_Esgk_PlaneCurveIntrinsicCellCover__intrinsicCover_incidence_sqRadius X pq ij hinc
  have hcut : H.cuts.card ≤ d * j := by
    calc
      H.cuts.card ≤ P.card / k := H.cuts_card_le
      _ ≤ S.card / k := Nat.div_le_div_right (planeCurveSafeSample_card_le G o S)
      _ ≤ d * j := intrinsicPartitionBlockSize_cut_bound hd hj hN
  have hcells : (cells.card : ℝ) ≤ 2 * (d : ℝ) ^ 2 * (j : ℝ) ^ 2 := by
    have hbound := intrinsicPartition_cell_count_le hj hcut
      (by simpa only [pow_two, mul_assoc] using H.arcs_card_le)
    have hcard : cells.card = H.arcs.card ^ 2 := by
      simp only [cells, Finset.card_product, pow_two]
    rw [hcard]
    exact_mod_cast hbound
  have htargetload : ∀ A ∈ H.arcs, (targets A).card ≤ k := by
    intro A hA
    exact (planeCurveSafeSample_subtype_filter_card_le G o S X.P₂ hP₂
      (H.arc_properties A hA).2.2.2.1).trans (H.arc_properties A hA).2.2.2.2.2
  have hpoints : ∀ C ∈ cells, ((points C).card : ℝ) ≤
      4 * (S.card : ℝ) ^ 2 / ((d : ℝ) ^ 2 * (j : ℝ) ^ 2) := by
    intro C hC
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hC
    have hcard : (points C).card ≤ k ^ 2 := by
      simpa only [points, Finset.card_product, pow_two] using
        Nat.mul_le_mul (htargetload C.1 hA) (htargetload C.2 hB)
    exact le_trans (by exact_mod_cast hcard)
      (intrinsicPartitionBlockSize_sq_le hd hj hN)
  have hvisit (ij : X.P₁ × X.P₁) :
      (planeCurveArcPairVisits H.arcs ij.1 ij.2).card ≤ 20 * d * d * j := by
    have hbound := planeCurveArcPairVisits_card_le_of_sample H hG hdegree hmax hnot
      S hS hsize ij.1 ij.2 (hcritical ij.1).1 (hcritical ij.1).2
        (hcritical ij.2).1 (hcritical ij.2).2
    apply le_trans hbound
    apply le_trans _ (intrinsicPartition_visit_count_le hj hcut)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ H.boundary_card_le) _))
  have hsum : (∑ C ∈ cells, (labels C).card) =
      ∑ ij : X.P₁ × X.P₁, (planeCurveArcPairVisits H.arcs ij.1 ij.2).card := by
    have hcount := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := cells) (t := (Finset.univ : Finset (X.P₁ × X.P₁)))
      (fun C ij ↦ C ∈ planeCurveArcPairVisits H.arcs ij.1 ij.2)
    change (∑ C ∈ cells, (labels C).card) = _ at hcount
    rw [hcount]
    apply Finset.sum_congr rfl
    intro ij _
    congr 1
    ext C
    rw [Finset.mem_bipartiteBelow]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨(Finset.mem_filter.mp h).1, h⟩⟩
  have hlabelsNat : (∑ C ∈ cells, (labels C).card) ≤
      20 * d ^ 2 * j * S.card ^ 2 := by
    rw [hsum]
    calc
      _ ≤ ∑ _ij : X.P₁ × X.P₁, 20 * d * d * j :=
        Finset.sum_le_sum (fun ij _ ↦ hvisit ij)
      _ = X.P₁.card ^ 2 * (20 * d * d * j) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          Fintype.card_coe, smul_eq_mul, pow_two]
      _ ≤ S.card ^ 2 * (20 * d * d * j) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Finset.card_le_card hP₁) 2)
      _ = 20 * d ^ 2 * j * S.card ^ 2 := by ring
  apply nonempty_intrinsicAuxiliaryCellCover_of_finite_index X cells points labels exceptional
    hexceptional hcovers hlabels hcells hpoints
  exact_mod_cast hlabelsNat


theorem maximallyCircularIntrinsicCellCover :
    MaximallyCircularIntrinsicCellCoverStatement := by
  intro G S X hG _habs hnot hmax hS _hself _hcarrier _hdisjoint hpart
    _hbalance₁ _hbalance₂ _hpositive j hj hN
  have hd : 2 ≤ G.totalDegree := hmax.two_le_totalDegree_of_irreducible hG
  have hdpos : 0 < G.totalDegree := by omega
  have hsize : G.totalDegree * (G.totalDegree - 1) < S.card := by
    have hpred := Nat.mul_le_mul_left G.totalDegree (Nat.sub_le G.totalDegree 1)
    have hscale : G.totalDegree * G.totalDegree ≤ j * G.totalDegree :=
      Nat.mul_le_mul_right G.totalDegree (by omega)
    exact lt_of_le_of_lt (hpred.trans hscale) hN
  have hsize₂ : 2 ≤ S.card := by
    have hjpos : 0 < j := by omega
    nlinarith
  have hS' : ∀ p ∈ S, p ∈ PlaneCurveZeroSet G := fun _ hp ↦ hS hp
  obtain ⟨ε, hε, _hcut, hbelow, hcutfin, hcutcard, hcritical⟩ :=
    exists_planeCurve_safe_cutoff_and_critical_bounds hG le_rfl hmax hnot S hS' hsize
  have hP₁ : X.P₁ ⊆ S := by
    rw [← hpart]
    exact Finset.subset_union_left
  have hP₂ : X.P₂ ⊆ S := by
    rw [← hpart]
    exact Finset.subset_union_right
  obtain ⟨H⟩ := nonempty_planeCurveArcPartition hε (0 : PachDeZeeuw.Algebraic.Point2)
    hcutfin hcutcard (hcritical 0).2.1 (hcritical 0).2.2
    (planeCurveSafeSample G 0 S) (planeCurveSafeSample_subset_safe G 0 S hbelow)
    (intrinsicPartitionBlockSize G.totalDegree j S.card)
    (intrinsicPartitionBlockSize_pos hdpos hj hN)
  exact nonempty_intrinsicAuxiliaryCellCover_of_arcPartition 0 S X hG le_rfl
    hmax hnot hS' hsize₂ hP₁ hP₂ hdpos hj hN hbelow (fun a ↦ (hcritical a).2) H

end Esgk
end

end


section
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk


theorem maximally_circular_intrinsic_cell_cover :
    MaximallyCircularIntrinsicCellCoverStatement := by
  exact maximallyCircularIntrinsicCellCover


theorem maximally_circular_restricted_raw_auxiliary_incidence_bound :
    MaximallyCircularRestrictedRawAuxiliaryIncidenceStatement := by
  exact maximallyCircularRestrictedRawAuxiliaryIncidence_of_intrinsicCellCover
    maximally_circular_intrinsic_cell_cover


end Esgk

end


/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open Esgk
section


theorem solution :
    MaximallyCircularRawAuxiliaryIncidenceStatement := by
  exact maximallyCircularRestrictedRawAuxiliaryIncidence_to_raw
    maximally_circular_restricted_raw_auxiliary_incidence_bound


end
