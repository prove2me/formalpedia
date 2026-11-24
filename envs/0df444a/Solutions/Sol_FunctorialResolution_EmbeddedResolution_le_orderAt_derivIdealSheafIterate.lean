-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_orderAt_derivIdealSheafIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:55:42.825641+00:00
-- url     : https://prove2.me/submissions/e4ba11e1-34d8-4975-bf3a-1d72e2113be8

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafOrderDecrease
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_stalkIdeal_derivIdealSheafIterate
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_le_pow_of_le_pow
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_orderAt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (x : X) (n r : ℕ) (h : ((n + r : ℕ) : ℕ∞) ≤ orderAt I x) :
    (n : ℕ∞) ≤ orderAt (derivIdealSheafIterate k p r I) x := by
  rw [le_orderAt_iff] at h ⊢
  rw [stalkIdeal_derivIdealSheafIterate k p r I x]
  have key := @derivIdealIterate_le_pow_of_le_pow k _ _ _ (stalkAlgebra k p x)
    (stalkIdeal I x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (n + r) r h
  rwa [Nat.add_sub_cancel] at key
end FunctorialResolution.EmbeddedResolution
