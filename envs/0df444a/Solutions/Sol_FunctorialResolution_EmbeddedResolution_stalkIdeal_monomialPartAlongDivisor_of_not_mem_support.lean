-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_monomialPartAlongDivisor_of_not_mem_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:00.530601+00:00
-- url     : https://prove2.me/submissions/1684d772-ed70-4d35-a30a-a6571496424e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateDivisorSmoothness
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IrreducibleComponentsOfSupport
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_OrderAtGenericPoint
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialSplitting
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MonomialCase_MonomialPartAlongDivisor
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_componentPowerIdeal_of_not_mem
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_monomialPartAlongDivisor_eq_inf_componentPowerIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_finite_isIrreducibleComponentOfSupport
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_iff_forall_stalkIdeal_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_top

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
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
private theorem idealSheafData_mul_le_left (a b : X.IdealSheafData) : a * b ≤ a := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r hr s _ => Ideal.mul_mem_right s _ hr
private theorem idealSheafData_mul_le_right (a b : X.IdealSheafData) : a * b ≤ b := by
  rw [le_iff_forall_stalkIdeal_le]
  intro x
  rw [stalkIdeal_mul]
  exact Ideal.mul_le.mpr fun r _ s hs => Ideal.mul_mem_left _ r hs
private theorem stalkIdeal_inf_eq_top (a b : X.IdealSheafData) (x : X)
    (ha : stalkIdeal a x = ⊤) (hb : stalkIdeal b x = ⊤) :
    stalkIdeal (a ⊓ b) x = ⊤ := by
  refine le_antisymm le_top ?_
  have hmono := stalkIdeal_mono
    (le_inf (idealSheafData_mul_le_left a b) (idealSheafData_mul_le_right a b)) x
  rw [stalkIdeal_mul, ha, hb] at hmono
  have htop : (⊤ : Ideal (X.presheaf.stalk x)) * ⊤ = ⊤ := by
    rw [← Ideal.one_eq_top, one_mul]
  rwa [htop] at hmono
private theorem stalkIdeal_finsetInf_eq_top {β : Type u} (f : β → X.IdealSheafData) (x : X)
    (s : Finset β) : (∀ b ∈ s, stalkIdeal (f b) x = ⊤) → stalkIdeal (s.inf f) x = ⊤ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.inf_empty]
    exact stalkIdeal_top x
  · intro a t ha ih hs
    rw [Finset.inf_insert]
    exact stalkIdeal_inf_eq_top _ _ x (hs a (Finset.mem_insert_self a t))
      (ih fun b hb => hs b (Finset.mem_insert_of_mem hb))
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
variable {k : Type u} [Field k]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution [TopologicalSpace.NoetherianSpace ↥X]
    (I D : X.IdealSheafData) {x : X} (hx : x ∉ (D.support : Set X)) :
    stalkIdeal (monomialPartAlongDivisor I D) x = ⊤ := by
  rw [monomialPartAlongDivisor_eq_inf_componentPowerIdeal]
  refine stalkIdeal_finsetInf_eq_top (fun C => componentPowerIdeal I D C) x
    (supportComponentsFinset D) ?_
  intro C hC
  have hCmem : IsIrreducibleComponentOfSupport D C :=
    (Set.Finite.mem_toFinset (finite_isIrreducibleComponentOfSupport D)).mp hC
  exact stalkIdeal_componentPowerIdeal_of_not_mem I D C (fun hxC => hx (hCmem.subset_support hxC))
end FunctorialResolution.EmbeddedResolution
