-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.EZ_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:17.064092+00:00
-- url     : https://prove2.me/submissions/8922b197-4e07-4332-8363-e7a27f736663

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_of_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_lin
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_smul_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_EZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add


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
theorem _root_.solution {Φ : Mat k r → E} {g : Mat k r} (hloc : Loc 2 Φ g) (hgG : g ∈ GV k r) (Z : Mat k r)
    (y : ℂ) (q d : Fin (2 * r + k + 1)) :
    EZ Z (Top (LT (Msg k r)) y q d Φ) g =
      (if q = d then (1 : ℂ) else 0) • (y • EZ Z Φ g) + EZ Z (EZ (Msg k r q d) Φ) g := by
  have hΦ1 : Loc 1 Φ g := loc_mono (by norm_num) hloc
  have h11 : Loc (1 + 1) Φ g := by rw [one_add_one_eq_two]; exact hloc
  by_cases hqd : q = d
  · have e : Top (LT (Msg k r)) y q d Φ = fun x => y • Φ x + (1 : ℂ) • EZ (Msg k r q d) Φ x := by
      funext x; simp [top_apply'', hqd]
    have hy1 : Loc 1 (fun x => y • Φ x) g := loc_of_eq (by funext x; simp) (loc_add (loc_zero 1 g) hΦ1 y)
    rw [e, EZ_lin hy1 (loc_EZ _ h11) hgG, EZ_smul_fun hΦ1 hgG]
    simp [hqd]
  · have e : Top (LT (Msg k r)) y q d Φ = EZ (Msg k r q d) Φ := by
      funext x; simp [top_apply'', hqd]
    rw [e]
    simp [hqd]
end Formalism.FourierDecayAlt.P.FourTermExpansion
