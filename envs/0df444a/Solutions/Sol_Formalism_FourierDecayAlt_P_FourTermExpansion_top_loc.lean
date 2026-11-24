-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FourTermExpansion.top_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:03:01.85096+00:00
-- url     : https://prove2.me/submissions/5623e9a1-1db2-4331-ac1e-4cf2ad016caf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LieDecompositionLocal
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_of_eq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d
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
variable (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r)
namespace Formalism.FourierDecayAlt.P.FourTermExpansion
theorem _root_.solution {m : ℕ∞} {Φ : Mat k r → E} {g : Mat k r} (h : Loc (m + 1) Φ g) (v : ℂ)
    (a b : Fin (2 * r + k + 1)) : Loc m (Top (LT M) v a b Φ) g := by
  have hΦ : Loc m Φ g := loc_mono le_self_add h
  have h1 : Loc m (fun x => if a = b then v • Φ x else 0) g := by
    by_cases hab : a = b
    · exact loc_of_eq (by funext x; simp [hab]) (loc_add (loc_zero m g) hΦ v)
    · exact loc_of_eq (by funext x; simp [hab]) (loc_zero m g)
  exact loc_of_eq (by funext x; simp [top_apply'']) (loc_add h1 (loc_EZ (M a b) h) 1)
end Formalism.FourierDecayAlt.P.FourTermExpansion
