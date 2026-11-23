-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.card_PG
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:39.617367+00:00
-- url     : https://prove2.me/submissions/2c7e2943-4746-4c14-aea6-73a02af995dc

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_prodG
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_phi_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_disj_phi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (V : Subgroup (GL (Fin k) A)) :
    Nat.card (PG r V) = Nat.card (UcG A (cI r k)) * Nat.card V := by
  rw [PG, card_prodG _ _ _ (disj_phi V), Subgroup.card_map_of_injective phi_injective]
end Formalism.FourierDecayAlt.P.S3x2
