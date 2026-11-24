-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.prj_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:36:30.430067+00:00
-- url     : https://prove2.me/submissions/14383fcb-c674-4e8c-815f-089b446f540c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_hpk_herm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux1_hpk_sq__7d0cb96087ff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution (Z : Mat k r) : inLie k r (prj Z) := by
  unfold inLie prj
  have hH := (hpk_herm (k := k) (r := r))
  have hHH := (hpk_sq' (k := k) (r := r))
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH,
    conjTranspose_conjTranspose]
  have h1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one]
  have h2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2, ← smul_add]
  simp
end Formalism.FourierDecayAlt.P.Ux1
