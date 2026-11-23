-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.lowJ_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:48.950212+00:00
-- url     : https://prove2.me/submissions/e705fa33-7897-4913-9cd6-c45b9310828f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_lowJ_m
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
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (V : lowW K w.1 w.2) : ∃ v ξ, V = lowJ hN hW v ξ := by
  obtain ⟨A, B, C, D, hM⟩ : ∃ A B C D, ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
      blkM hN A B C D := ⟨_, _, _, _, eq_blkM hN _⟩
  obtain ⟨hL, H, hH, e⟩ := V.2
  rw [hM] at hL e
  obtain ⟨hA, rfl, hD⟩ := (blkM_isLowUni _ _ _ _ _).1 hL
  obtain ⟨⟨-, hAm⟩, ⟨-, hDm⟩⟩ := (low_mem hN hW A C D).1 ⟨hL, H, hH, e⟩
  have hAd := isLowUni_det K hA
  have hDd := isLowUni_det K hD
  have m1 : IsLowUni ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) ∧
      ∃ H' : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H' ∧
        ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) * pt h.1 h.2 =
          pt h.1 h.2 * H' := by
    rw [sec_gl_coe]
    exact ⟨hA, hAm⟩
  have m2 : IsLowUni ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) ∧
      ∃ H' : Matrix (Fin g.1.sum) (Fin g.1.sum) K, IsLowUni H' ∧
        ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) * pt g.1 g.2 =
          pt g.1 g.2 * H' := by
    rw [sec_gl_coe]
    exact ⟨hD, hDm⟩
  refine ⟨(⟨sec_gl A hAd, m1⟩, ⟨sec_gl D hDd, m2⟩), C * A⁻¹, sec_m_ext ?_⟩
  rw [lowJ_m]
  simp only [sec_m, sec_gl_coe]
  rw [hM, Matrix.mul_assoc, Matrix.nonsing_inv_mul A (by rw [hAd]; exact isUnit_one), Matrix.mul_one]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
