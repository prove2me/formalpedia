-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheaf_pow_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:20:10.087454+00:00
-- url     : https://prove2.me/submissions/2cf2f728-745d-48c0-89cb-00f7f849dc6e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_pow_succ_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap


attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData) (n : ℕ) :
    derivIdealSheaf k p (I ^ (n + 1)) ≤ I ^ n * derivIdealSheaf k p I := by
  have key : ∀ U : X.affineOpens,
      (derivIdealSheaf k p (I ^ (n + 1))).ideal U ≤ (I ^ n * derivIdealSheaf k p I).ideal U := by
    intro U
    have hmul : ∀ A B : X.IdealSheafData, (A * B).ideal U = A.ideal U * B.ideal U := by
      intro A B
      simp [Scheme.IdealSheafData.ideal_mul]
    have hpow : ∀ m : ℕ, (I ^ m).ideal U = I.ideal U ^ m := fun m =>
      congrFun (Scheme.IdealSheafData.ideal_pow I m) U
    rw [hmul, derivIdealSheaf_ideal, derivIdealSheaf_ideal, hpow, hpow]
    exact @derivIdeal_pow_succ_le k _ _ _ (sectionsAlgebra k p U.1) (I.ideal U) n
  exact key
end FunctorialResolution.EmbeddedResolution
