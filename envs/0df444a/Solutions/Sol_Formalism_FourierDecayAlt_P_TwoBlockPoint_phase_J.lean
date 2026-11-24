-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.phase_J
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:57.991102+00:00
-- url     : https://prove2.me/submissions/f3f8aa68-d075-4046-ad5e-c06df918fbd7

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sLow_blkM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_sUp_blkM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornL_mul_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_upJ_m
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (v : lowW K h.1 h.2 × lowW K g.1 g.2)
    (u : upUniG K h.1.sum × upUniG K g.1.sum)
    (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    phase ψ ((lowJ hN hW v X, upJ hN u Y) : lowW K w.1 w.2 × upUniG K w.1.sum) =
      phase ψ ((v.1, u.1) : lowW K h.1 h.2 × upUniG K h.1.sum) * ψ (cornL X + cornU Y) *
        phase ψ ((v.2, u.2) : lowW K g.1 g.2 × upUniG K g.1.sum) := by
  simp only [phase]
  rw [show ((lowJ hN hW v X : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = _ from
      lowJ_m hN hW v X,
    show ((upJ hN u Y : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) = _ from upJ_m hN u Y,
    sLow_blkM, sUp_blkM, cornL_mul_low v.1.2.1, cornU_mul_up u.1.2,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.TwoBlockPoint
