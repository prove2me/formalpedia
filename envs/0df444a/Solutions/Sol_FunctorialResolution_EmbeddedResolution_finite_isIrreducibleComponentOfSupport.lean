-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.finite_isIrreducibleComponentOfSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:57:56.571144+00:00
-- url     : https://prove2.me/submissions/c438e292-9bbd-4d1b-bae7-a15fa18dcd74

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_PowerContainmentAndOrderLocus
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem isPreirreducible_of_isPreirreducible_image_val {α : Type u} [TopologicalSpace α] {s : Set α}
    {T : Set s} (h : IsPreirreducible (Subtype.val '' T)) : IsPreirreducible T := by
  intro u v hu hv hTu hTv
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨a, haT, hau⟩ := hTu
  obtain ⟨b, hbT, hbv⟩ := hTv
  obtain ⟨w, ⟨t, htT, rfl⟩, hwu, hwv⟩ :=
    h u' v' hu' hv' ⟨(a : α), ⟨a, haT, rfl⟩, hau⟩ ⟨(b : α), ⟨b, hbT, rfl⟩, hbv⟩
  exact ⟨t, htT, hwu, hwv⟩
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
end IsIrreducibleComponentOfSupport
namespace IsIrreducibleComponentOfSupport
variable {X : Scheme.{u}} {D : X.IdealSheafData} {C : Set X}
variable {k : Type u} [Field k]
end IsIrreducibleComponentOfSupport
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} [TopologicalSpace.NoetherianSpace ↥X]
    (D : X.IdealSheafData) :
    {C : Set X | IsIrreducibleComponentOfSupport D C}.Finite := by
  have hfin : (irreducibleComponents ↥((D.support : Set X))).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have himg : ∀ C ∈ {C : Set X | IsIrreducibleComponentOfSupport D C},
      (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) ∈
        irreducibleComponents ↥((D.support : Set X)) := by
    intro C hC
    have hCsub : C ⊆ (D.support : Set X) := hC.subset_support
    have himgC :
        (Subtype.val '' (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) : Set ↥X) = C :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hCsub)
    have hirr : IsIrreducible (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))) := by
      obtain ⟨y, hy⟩ := hC.isIrreducible.nonempty
      refine ⟨⟨⟨y, hCsub hy⟩, hy⟩, ?_⟩
      apply isPreirreducible_of_isPreirreducible_image_val
      rw [himgC]
      exact hC.isIrreducible.2
    refine ⟨hirr, ?_⟩
    intro T' hT' hle
    have h1 : IsIrreducible (Subtype.val '' T' : Set ↥X) :=
      hT'.image _ continuous_subtype_val.continuousOn
    have h2 : (Subtype.val '' T' : Set ↥X) ⊆ (D.support : Set X) := by
      rintro _ ⟨t, _, rfl⟩
      exact t.2
    have h3 : C ⊆ (Subtype.val '' T' : Set ↥X) := by
      rw [← himgC]
      exact Set.image_mono hle
    have h4 := hC.maximal _ h1 h3 h2
    intro t ht
    have hmem : (t : ↥X) ∈ C := by rw [← h4]; exact ⟨t, ht, rfl⟩
    exact hmem
  have hsub : (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X)))) ''
      {C : Set X | IsIrreducibleComponentOfSupport D C} ⊆ irreducibleComponents ↥((D.support : Set X)) := by
    rintro _ ⟨C, hC, rfl⟩
    exact himg C hC
  have hinj : Set.InjOn (fun C : Set X => (Subtype.val ⁻¹' C : Set ↥((D.support : Set X))))
      {C : Set X | IsIrreducibleComponentOfSupport D C} := by
    intro C1 h1 C2 h2 heq
    have e1 :
        (Subtype.val '' (Subtype.val ⁻¹' C1 : Set ↥((D.support : Set X))) : Set ↥X) = C1 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h1.subset_support)
    have e2 :
        (Subtype.val '' (Subtype.val ⁻¹' C2 : Set ↥((D.support : Set X))) : Set ↥X) = C2 :=
      Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact h2.subset_support)
    rw [← e1, ← e2]
    exact congrArg (Set.image Subtype.val) heq
  exact Set.Finite.of_finite_image (hfin.subset hsub) hinj
end FunctorialResolution.EmbeddedResolution
