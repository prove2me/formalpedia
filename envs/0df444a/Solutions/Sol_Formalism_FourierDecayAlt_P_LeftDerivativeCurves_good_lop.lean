-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.good_lop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:52:58.601913+00:00
-- url     : https://prove2.me/submissions/b6ba92f5-c658-4d73-8c80-82fac5b662e2

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_good_LZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
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
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution (hD : IsOpen D) {Z : Mx k r} (h1 : inLieLev k r i (hpart1 (Hpk k r) Z))
    (h2 : inLieLev k r i (hpart2 (Hpk k r) Z)) (c : ℂ) : Good k r i D (lop (E := E) k r c Z) := by
  exact (good_LZ hD h1 h2).add (Qx2.good_id.smul c)
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
