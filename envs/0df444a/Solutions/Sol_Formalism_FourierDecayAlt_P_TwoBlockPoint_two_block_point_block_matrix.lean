-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.two_block_point_block_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:28.947802+00:00
-- url     : https://prove2.me/submissions/34733d02-961b-4463-9659-0dcec0558570

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
theorem _root_.solution (h : Point K) (m : ℕ) (t c : Kˣ) :
    pt (pt2 h m t c).1 (pt2 h m t c).2 =
      blkM (two_block_point_size_sum h m t c) (pt h.1 h.2) 0 0
        (pt (pt2 (h0 : Point K) m t c).1 (pt2 (h0 : Point K) m t c).2) := by
  refine pt_append' _ h.1 _ ?_ _ h.2 _ ?_ ?_ (two_block_point_size_sum h m t c)
  · simp [pt2, h0, addBlock]
  · intro b hb
    simp [pt2, addBlock, Function.update_apply, show b ≠ h.1.length by omega,
      show b ≠ h.1.length + 1 by omega]
  · intro b hb
    have hb2 : b < 2 := by simpa [pt2, h0, addBlock] using hb
    interval_cases b <;> simp [pt2, h0, addBlock, Function.update_apply]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
