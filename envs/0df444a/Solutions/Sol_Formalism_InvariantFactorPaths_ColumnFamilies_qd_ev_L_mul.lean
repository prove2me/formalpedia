-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_ev_L_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:45.908161+00:00
-- url     : https://prove2.me/submissions/98536965-466e-48a3-8b95-2814e61cd1f8

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_EqSmulCanonicalOfUnipotentInvariant
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_map
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_aeval_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_L_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGLR_mapCoord
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_evGL_detU
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_ev_sig


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {R' : Type} [CommRing R'] [Algebra ℚ R'] (x : GL (Fin n) R') (γ : GL (Fin n) ℚ) (mu : Fin n → ℤ)
    (P : MvPolynomial (Fin n × Fin n) ℚ) :
    evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_L mu P)
      = evGLR (R := ℚ) x (qd_L mu
        (((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) • rowAct ℚ γ.val.transpose P)) := by
  rw [map_smul, qd_L_apply, qd_L_apply, map_mul, qd_ev_sig, qd_aeval_mul, Algebra.smul_def, map_mul, map_mul,
    qd_ev_sig]
  have h1 : evGLR (R := ℚ) (x * Matrix.GeneralLinearGroup.map (algebraMap ℚ R') γ) (qd_U mu)
      = evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        * evGLR (R := ℚ) x (qd_U mu) := by
    have h2 : evGLR (R := ℚ) x (algebraMap ℚ (GLCoord ℚ n) ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ))
        = algebraMap ℚ R' ((Matrix.GeneralLinearGroup.det γ ^ mu (lastIdx n) : ℚˣ) : ℚ) :=
      qd_ev_algebraMap x _
    rw [h2, ← qd_evGL_detU, ← qd_evGL_map]
    unfold qd_U
    rw [qd_evGLR_mapCoord, qd_evGLR_mapCoord, qd_evGL_detU, qd_evGL_detU, qd_evGL_detU, map_mul, mul_zpow,
      Units.val_mul, mul_comm]
  rw [h1]
  ring
end Formalism.InvariantFactorPaths.ColumnFamilies
