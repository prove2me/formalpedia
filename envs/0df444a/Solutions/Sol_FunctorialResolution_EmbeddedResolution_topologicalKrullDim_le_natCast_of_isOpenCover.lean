-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.topologicalKrullDim_le_natCast_of_isOpenCover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:57.748135+00:00
-- url     : https://prove2.me/submissions/a3a17f64-0249-47f4-8a7b-49cd3c371cc6

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_KrullDimClosedSubset
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_FiniteKrullDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open TopologicalSpace AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem subset_closure_inter_of_isPreirreducible {X : Type u} [TopologicalSpace X]
    {S V : Set X} (hS : IsPreirreducible S) (hV : IsOpen V) (hne : (S ∩ V).Nonempty) :
    S ⊆ closure (S ∩ V) := by
  intro s hs
  rw [mem_closure_iff]
  intro W hW hsW
  obtain ⟨y, hyS, hyW, hyV⟩ := hS W V hW hV ⟨s, hs, hsW⟩ hne
  exact ⟨y, hyW, hyS, hyV⟩
private theorem eq_of_preimage_val_eq {X : Type u} [TopologicalSpace X] {W : Set X}
    (hW : IsOpen W) {C D : Set X} (hC : IsClosed C) (hD : IsIrreducible D) (hCsubD : C ⊆ D)
    (hne : (C ∩ W).Nonempty)
    (heq : (Subtype.val ⁻¹' C : Set ↥W) = (Subtype.val ⁻¹' D : Set ↥W)) : C = D := by
  refine subset_antisymm hCsubD ?_
  have h1 : D ∩ W ⊆ C := by
    rintro y ⟨hyD, hyW⟩
    have hy : (⟨y, hyW⟩ : ↥W) ∈ (Subtype.val ⁻¹' D : Set ↥W) := hyD
    rw [← heq] at hy
    exact hy
  obtain ⟨z, hzC, hzW⟩ := hne
  have h2 : (D ∩ W).Nonempty := ⟨z, hCsubD hzC, hzW⟩
  calc D ⊆ closure (D ∩ W) := subset_closure_inter_of_isPreirreducible hD.2 hW h2
    _ ⊆ closure C := closure_mono h1
    _ = C := hC.closure_eq
private theorem topologicalKrullDim_le_of_iUnion_eq_univ {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ)
    (c : WithBot ℕ∞) (h : ∀ i, topologicalKrullDim ↥(U i) ≤ c) :
    topologicalKrullDim X ≤ c := by
  refine iSup_le ?_
  intro p
  obtain ⟨x, hx⟩ := (p 0).isIrreducible.1
  have hxU : x ∈ ⋃ i, U i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
  have hoe := (hU i).isOpenEmbedding_subtypeVal
  have hsub : ∀ j : Fin (p.length + 1),
      ((p 0 : IrreducibleCloseds X) : Set X) ⊆ ((p j : IrreducibleCloseds X) : Set X) :=
    fun j => SetLike.coe_subset_coe.mpr (LTSeries.monotone p (Fin.zero_le j))
  let V : Fin (p.length + 1) → IrreducibleCloseds ↥(U i) := fun j =>
    ⟨Subtype.val ⁻¹' ((p j : IrreducibleCloseds X) : Set X),
      ⟨⟨⟨x, hi⟩, hsub j hx⟩, (p j).isIrreducible.2.preimage hoe⟩,
      (p j).isClosed.preimage continuous_subtype_val⟩
  have hstep : ∀ j : Fin p.length, V j.castSucc < V j.succ := by
    intro j
    have hlt : p j.castSucc < p j.succ := p.step j
    have hsubset : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        ⊆ ((p j.succ : IrreducibleCloseds X) : Set X) :=
      SetLike.coe_subset_coe.mpr hlt.le
    have hle : V j.castSucc ≤ V j.succ := by
      refine SetLike.coe_subset_coe.mp ?_
      intro z hz
      exact hsubset hz
    refine lt_of_le_of_ne hle ?_
    intro hEq
    have hcar : (Subtype.val ⁻¹' ((p j.castSucc : IrreducibleCloseds X) : Set X) : Set ↥(U i))
        = (Subtype.val ⁻¹' ((p j.succ : IrreducibleCloseds X) : Set X) : Set ↥(U i)) :=
      congrArg (fun s : IrreducibleCloseds ↥(U i) => (s : Set ↥(U i))) hEq
    have hCsubD : ((p j.castSucc : IrreducibleCloseds X) : Set X)
        = ((p j.succ : IrreducibleCloseds X) : Set X) :=
      eq_of_preimage_val_eq (hU i) (p j.castSucc).isClosed (p j.succ).isIrreducible hsubset
        ⟨x, hsub _ hx, hi⟩ hcar
    exact absurd (IrreducibleCloseds.ext hCsubD) hlt.ne
  let q : LTSeries (IrreducibleCloseds ↥(U i)) := ⟨p.length, V, hstep⟩
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim ↥(U i) :=
    Order.LTSeries.length_le_krullDim q
  exact le_trans hq (h i)
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u v
open TopologicalSpace AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Type u} [TopologicalSpace X] {ι : Type v}
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) (hcov : ⋃ i, U i = Set.univ) (n : ℕ)
    (h : ∀ i, topologicalKrullDim ↥(U i) ≤ (n : WithBot ℕ∞)) :
    topologicalKrullDim X ≤ (n : WithBot ℕ∞) :=
  topologicalKrullDim_le_of_iUnion_eq_univ U hU hcov _ h
end FunctorialResolution.EmbeddedResolution
