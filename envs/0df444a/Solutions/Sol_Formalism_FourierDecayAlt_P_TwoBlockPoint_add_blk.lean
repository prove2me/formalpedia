-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.add_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:28.031903+00:00
-- url     : https://prove2.me/submissions/100aef4b-2e0c-40c4-9710-ccbf177d6336

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_pt_append__77a8e803be09
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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (h : Point K) (s : ℕ) (z : Kˣ) :
    pt (addBlock h s z).1 (addBlock h s z).2 =
      blkM (add_sum h s z) (pt h.1 h.2) 0 0
        (pt (addBlock (h0 : Point K) s z).1 (addBlock (h0 : Point K) s z).2) := by
  refine pt_append' _ h.1 _ ?_ _ h.2 _ ?_ ?_ (add_sum h s z)
  · simp [addBlock, h0]
  · intro b hb
    exact Function.update_of_ne (Nat.ne_of_lt hb) _ _
  · intro b hb
    have hb0 : b = 0 := by simpa [addBlock, h0] using hb
    subst hb0
    simp [addBlock, h0]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
