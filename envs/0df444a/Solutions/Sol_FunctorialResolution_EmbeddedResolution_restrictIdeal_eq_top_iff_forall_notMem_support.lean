-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:24:18.447139+00:00
-- url     : https://prove2.me/submissions/b6894bf9-da9e-4916-9158-c86946612c60

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Theorems.Thm_P2M_FunctorialResolution_EmbeddedResolution_restrictIdeal_eq_comap___a4ce28546e44

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) :
    restrictIdeal I U = ⊤ ↔ ∀ x : X, x ∈ U → x ∉ I.support := by
  have hbot : ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) = ∅ := rfl
  have hbot' : ∀ A : TopologicalSpace.Closeds U.toScheme,
      (A = ⊥ ↔ ∀ y : U.toScheme, y ∉ A) := by
    intro A
    constructor
    · rintro rfl y hy
      have hy' : y ∈ ((⊥ : TopologicalSpace.Closeds U.toScheme) : Set U.toScheme) := hy
      rw [hbot] at hy'
      exact hy'
    · intro hall
      have hA : (A : Set U.toScheme) = ∅ :=
        Set.Subset.antisymm (fun y hy => absurd hy (hall y)) (Set.empty_subset _)
      exact SetLike.coe_injective (hA.trans hbot.symm)
  have key : ∀ (x : X) (hx : x ∈ U),
      ((⟨x, hx⟩ : U.toScheme) ∈ (I.comap U.ι).support ↔ x ∈ I.support) := by
    intro x hx
    simp only [Scheme.IdealSheafData.support_comap]
    rfl
  rw [restrictIdeal_eq_comap_ι]
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, hbot']
  constructor
  · intro h x hx hmem
    exact h ⟨x, hx⟩ ((key x hx).mpr hmem)
  · rintro h ⟨x, hx⟩ hy
    exact h x hx ((key x hx).mp hy)
end FunctorialResolution.EmbeddedResolution
