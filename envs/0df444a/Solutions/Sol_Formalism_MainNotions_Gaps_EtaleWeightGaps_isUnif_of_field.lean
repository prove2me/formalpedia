-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.isUnif_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:31.773808+00:00
-- url     : https://prove2.me/submissions/9bfa8b93-38b4-45ea-84ea-b57a022f0006

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] [Algebra K A]
    [IsScalarTower O K A] [Algebra.IsIntegral K A] {ϖ : O} (hϖ : Irreducible ϖ) : IsUnif A ϖ where
  irreducible := hϖ
  isUnit := by
    rw [IsScalarTower.algebraMap_apply O K A]
    refine IsUnit.map _ (IsUnit.mk0 _ ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  denom := fun x => by
    obtain ⟨⟨d, hd⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors O) x (Algebra.IsIntegral.isIntegral (R := K) x)
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hd) hϖ
    refine ⟨n, ?_⟩
    have h2 : ϖ ^ n • x = (↑u⁻¹ : O) • (((u : O) * ϖ ^ n) • x) := by
      rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact (As O A).smul_mem hint _
end Formalism.MainNotions.Gaps.EtaleWeightGaps
