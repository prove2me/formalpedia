-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.inv_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:44:35.078514+00:00
-- url     : https://prove2.me/submissions/f3d24566-92e5-4364-a520-c8493a02fc82

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGHead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution {m : ℕ} (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hZ : Z.det ≠ 0) (b : Fin (m + 1)) :
    Z⁻¹ b (Fin.last m) = Z.det⁻¹ * ((-1) ^ (m + (b : ℕ)) * (Z.submatrix Fin.castSucc b.succAbove).det) := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    smul_eq_mul, Ring.inverse_eq_inv']
end Formalism.FourierDecayAlt.P.PBG
