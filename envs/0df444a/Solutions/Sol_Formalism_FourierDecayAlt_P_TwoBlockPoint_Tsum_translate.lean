-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.Tsum_translate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:44.397291+00:00
-- url     : https://prove2.me/submissions/8817f652-a21c-4fe0-bbc6-8b885cd085e5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Fz_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornL_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_bigZ_translate
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_blkM_isInt
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
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z1 : Matrix (Fin a) (Fin a) K)
    (X X1 : Matrix (Fin s) (Fin a) K) (Y Y1 : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) (hX : ∀ i j, (X1 - X) i j ∈ R) (hY : ∀ i j, (Y1 - Y) i j ∈ R) :
    Tsum R ψ Z' Z1 X1 Y1 G = Tsum R ψ Z' Z1 X Y G := by
  unfold Tsum
  have h1 : ∀ {n : ℕ}, IsInt R (1 : Matrix (Fin n) (Fin n) K) := by
    intro n i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [show X1 = X + (X1 - X) by abel, show Y1 = Y + (Y1 - Y) by abel, bigZ_translate,
    Fz_uni R Z' _ _ _ ((blkM_isLowUni rfl 1 0 (X1 - X) 1).2 ⟨isLowUni_one K, rfl, isLowUni_one K⟩)
      ((blkM_isInt rfl 1 0 (X1 - X) 1 R).2 ⟨h1, fun i j => by simp, hX, h1⟩)
      ((blkM_isUpUni rfl 1 (Y1 - Y) 0 1).2 ⟨isUpUni_one K, rfl, isUpUni_one K⟩)
      ((blkM_isInt rfl 1 (Y1 - Y) 0 1 R).2 ⟨h1, hY, fun i j => by simp, h1⟩),
    cornL_add, cornU_add,
    show cornL X + cornL (X1 - X) + (cornU Y + cornU (Y1 - Y)) =
      (cornL X + cornU Y) + (cornL (X1 - X) + cornU (Y1 - Y)) by ring,
    AddChar.map_add_eq_mul, hψ _ (add_mem (cornL_mem R hX) (cornU_mem R hY)), mul_one]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
