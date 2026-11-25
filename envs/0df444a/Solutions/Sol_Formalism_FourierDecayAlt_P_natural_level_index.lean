-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.natural_level_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:27.375963+00:00
-- url     : https://prove2.me/submissions/96950a09-1816-40fc-a46a-bd85346eb661

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_PG
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_PG_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_surjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_Kpp_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_Knat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.IndexKnat := by
  intro o _ _ _ r k L
  refine ⟨?_, ?_, ?_⟩
  · rw [Knat_eq L, Subgroup.index_comap_of_surjective _ (red_surjective o _), card_S,
      Subgroup.index_mul_card]
  · rw [Kpp_eq L, Knat_eq L]
    exact Subgroup.comap_mono (PG_mono le_top)
  · rw [Kpp_eq L, Knat_eq L, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (red_surjective o _)]
    have h1 := Subgroup.relIndex_mul_relIndex ⊥ (PG r (upUniG (IsLocalRing.ResidueField o) k))
      (PG r ⊤) bot_le (PG_mono le_top)
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, card_PG, card_PG,
      Subgroup.card_top] at h1
    have hpos : 0 < Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) := Nat.card_pos
    have h2 : Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) *
        ((PG r (upUniG (IsLocalRing.ResidueField o) k)).relIndex (PG r ⊤) *
          Nat.card (upUniG (IsLocalRing.ResidueField o) k)) =
        Nat.card (UcG (IsLocalRing.ResidueField o) (cI r k)) *
          Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) := by
      rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h2
end Formalism.FourierDecayAlt.P
