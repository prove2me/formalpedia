-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.upJ_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:37.211805+00:00
-- url     : https://prove2.me/submissions/2f498982-8c3e-43d3-b5ea-cc8424d231e3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
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
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (V : upUniG K w.1.sum) : ∃ u η, V = upJ hN u η := by
  obtain ⟨A, B, C, D, hM⟩ : ∃ A B C D, ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) =
      blkM hN A B C D := ⟨_, _, _, _, eq_blkM hN _⟩
  have hU : IsUpUni ((V : GL (Fin w.1.sum) K) : Matrix (Fin w.1.sum) (Fin w.1.sum) K) := V.2
  rw [hM] at hU
  obtain ⟨hA, rfl, hD⟩ := (blkM_isUpUni _ _ _ _ _).1 hU
  have hAd := isUpUni_det K hA
  have hDd := isUpUni_det K hD
  have m1 : IsUpUni ((sec_gl A hAd : GL (Fin h.1.sum) K) : Matrix (Fin h.1.sum) (Fin h.1.sum) K) := by
    rw [sec_gl_coe]
    exact hA
  have m2 : IsUpUni ((sec_gl D hDd : GL (Fin g.1.sum) K) : Matrix (Fin g.1.sum) (Fin g.1.sum) K) := by
    rw [sec_gl_coe]
    exact hD
  refine ⟨(⟨sec_gl A hAd, m1⟩, ⟨sec_gl D hDd, m2⟩), A⁻¹ * B, sec_m_ext ?_⟩
  rw [upJ_m]
  simp only [sec_m, sec_gl_coe]
  rw [hM, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A (by rw [hAd]; exact isUnit_one), Matrix.one_mul]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
