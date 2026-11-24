-- Prove2me | solution 1 for Formalism.LatticeIndexTer.idxScale_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:57.288869+00:00
-- url     : https://prove2.me/submissions/d4076b85-e035-411d-9c4b-830862f9743d

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Lemmata_DiscreteValuationQuotients_LenQuotSpan
import Definitions.Def_Lemmata_GeneralBFactSecondExtra_Key
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_index_scalar_multiple_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.LatticeIndexTer
open Module
namespace Formalism.LatticeIndexTer
theorem _root_.solution (hB : LatBasis) : IdxScale := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ s N hN
  obtain ⟨bN, rfl⟩ := hB O K X N hN
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖK : algebraMap O K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ0
  have hu0 : algebraMap O K ϖ ^ (-s) ≠ 0 := zpow_ne_zero _ hϖK
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg s
  · rw [LatticeIndexDeterminant.index_scalar_multiple_eq bN _ hu0 1 (ϖ ^ (k * finrank K X)) one_ne_zero
      (pow_ne_zero _ hϖ0) (by
        rw [Fintype.card_fin, map_one, map_pow, zpow_neg, zpow_natCast, inv_pow, ← pow_mul,
          inv_mul_cancel₀ (pow_ne_zero _ hϖK)])]
    rw [IsDiscreteValuationRing.addVal_one, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
    simp
  · rw [LatticeIndexDeterminant.index_scalar_multiple_eq bN _ hu0 (ϖ ^ (k * finrank K X)) 1 (pow_ne_zero _ hϖ0) one_ne_zero (by
        rw [Fintype.card_fin, map_one, mul_one, map_pow, neg_neg, zpow_natCast, ← pow_mul])]
    rw [IsDiscreteValuationRing.addVal_one, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
    simp
end Formalism.LatticeIndexTer
