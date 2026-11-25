-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SignAntidiagonal.tau_eI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:46.344646+00:00
-- url     : https://prove2.me/submissions/1537e446-8170-4d25-9d90-2c31cb6f2b5c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneAddProjectionMemIsotropicSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianInsertionVectorOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_pe_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_ps_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_tau_val
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_tau_val
import Theorems.Thm_NFOne_sg_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.pe_val
attribute [local simp] Formalism.FourierDecayAlt.P.SignAntidiagonal.ps_val
attribute [local simp] NFOne.sg_val



set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants
noncomputable section
variable {k : ℕ}
variable (m : ℕ) (i : Fin (m + 1)) (Vc : Fin m → Fin (2 * (m + 1) + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
theorem _root_.solution (c : Fin (m + 1)) : WeylGroupFacts.tau k (m + 1) (eI k (m + 1) c) = esI k (m + 1) c := by
  have := c.isLt
  ext; rw [tau_val, if_pos (by left; simp only [eI]; omega)]; simp only [eI, esI]
end Formalism.FourierDecayAlt.P.SignAntidiagonal
