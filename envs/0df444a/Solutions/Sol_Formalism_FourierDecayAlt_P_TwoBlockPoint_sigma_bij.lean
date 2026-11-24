-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.sigma_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:08.048987+00:00
-- url     : https://prove2.me/submissions/9188f077-f832-40b2-b290-ef1ba21611c5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_low_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_up_bij
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
theorem _root_.solution : Function.Bijective (fun t => toCos R (sigma R hN hW t)) := by
  have hL := low_bij hN hW R
  have hU := up_bij hN R
  constructor
  · rintro ⟨⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩, X, Y⟩ ⟨⟨⟨l1', u1'⟩, ⟨l2', u2'⟩⟩, X', Y'⟩ e
    have i1 : ((l1, l2), X) = ((l1', l2'), X') := hL.1 (congrArg Prod.fst e)
    have i2 : ((u1, u2), Y) = ((u1', u2'), Y') := hU.1 (congrArg Prod.snd e)
    simp only [Prod.mk.injEq] at i1 i2
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := i1
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := i2
    rfl
  · intro q
    obtain ⟨⟨⟨a1, a2⟩, X⟩, hX⟩ := hL.2 q.1
    obtain ⟨⟨⟨b1, b2⟩, Y⟩, hY⟩ := hU.2 q.2
    exact ⟨(((a1, b1), (a2, b2)), (X, Y)), Prod.ext hX hY⟩
end Formalism.FourierDecayAlt.P.TwoBlockPoint
