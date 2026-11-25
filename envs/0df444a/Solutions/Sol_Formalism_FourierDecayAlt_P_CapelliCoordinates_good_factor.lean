-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.good_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:24:48.32083+00:00
-- url     : https://prove2.me/submissions/34585fdb-88df-4218-a57a-8f37e6c7b29c

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_Sup_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliCoordinates_Sup_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_Rep_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_good_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution {T : (Mx k r → E) → Mx k r → E} (hT : Qx2.Good k r i D T) (p : Prop) [Decidable p] (c : ℂ) :
    Qx2.Good k r i D (fun y : Mx k r → E => (if p then c • y else 0) + T y) := by
  by_cases hp : p
  · simp only [hp, ↓reduceIte]
    exact (Qx2.good_id.smul c).add hT
  · simp only [hp, ↓reduceIte, zero_add]
    exact hT
end Formalism.FourierDecayAlt.P.CapelliCoordinates
