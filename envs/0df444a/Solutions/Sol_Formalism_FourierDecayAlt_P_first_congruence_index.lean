-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.first_congruence_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:47:21.610885+00:00
-- url     : https://prove2.me/submissions/2efe960e-3842-48e2-8c15-7c6a3c5f2cda

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_pointwise_subgroup_le_parabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_card_s0G
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_card_sG
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_first_congruence_eq_reduction_comap
import Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_Knat_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_Knat_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_card_pointwise_stabiliser


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
open Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.FrameLevelIndices
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.CongruenceLevelIndex := by
  intro o _ _ _ r k L M
  refine ⟨?_, ?_⟩
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L]
    exact Subgroup.comap_mono pointwise_subgroup_le_parabolic
  · rw [first_congruence_eq_reduction_comap M, Knat_eq L, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (S3x2.red_surjective o _)]
    have : Fintype (IsLocalRing.ResidueField o) := Fintype.ofFinite _
    have h1 := Subgroup.relIndex_mul_relIndex ⊥
      (S3x1.s0G : Subgroup (GL (Idx r k) (IsLocalRing.ResidueField o)))
      (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))) bot_le pointwise_subgroup_le_parabolic
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, ← card_s0G, ← card_sG,
      card_pointwise_stabiliser (IsLocalRing.ResidueField o) r k, ← Nat.card_eq_fintype_card] at h1
    have hpos : 0 < Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsInertiaInfiniteCyclotomic x} := by
      rw [card_s0G]; exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
end Formalism.FourierDecayAlt.P
