-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.gl_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:00:50.896929+00:00
-- url     : https://prove2.me/submissions/c93298e5-3932-4ab1-85e6-495e37adfb1b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_single_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FourTermExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r)
    (a b c d : Fin (2 * r + k + 1)) :
    EZ (Msg k r a b) (EZ (Msg k r c d) Φ) g - EZ (Msg k r c d) (EZ (Msg k r a b) Φ) g =
      (if b = c then (1 : ℂ) else 0) • EZ (Msg k r a d) Φ g -
        (if d = a then (1 : ℂ) else 0) • EZ (Msg k r c b) Φ g := by
  rw [EZ_comm _ _ hloc hgG, single_comm, EZ_add (loc_mono (by norm_num) hloc) hgG,
    EZ_smul (loc_mono (by norm_num) hloc) hgG, EZ_smul (loc_mono (by norm_num) hloc) hgG, neg_smul,
    ← sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.FourTermExpansion
