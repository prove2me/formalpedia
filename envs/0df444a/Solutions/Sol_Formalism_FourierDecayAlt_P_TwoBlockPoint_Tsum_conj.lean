-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.Tsum_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:48:03.019837+00:00
-- url     : https://prove2.me/submissions/a6c7ca75-4aad-450e-af88-6ba540c84cc3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_blkM_isInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Fz_uni
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornL_low_mul
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_TwoBlockPoint_cornU_mul_up__9d33fb3090fc
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_bigZ_conj
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
theorem _root_.solution (ψ : AddChar K ℂ) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z1 : Matrix (Fin a) (Fin a) K)
    (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G v u : Matrix (Fin s) (Fin s) K) (hv : IsLowUni v) (hvi : IsInt R v) (hu : IsUpUni u)
    (hui : IsInt R u) :
    Tsum R ψ Z' Z1 (v * X) (Y * u) (v * G * u) = Tsum R ψ Z' Z1 X Y G := by
  unfold Tsum
  have h1 : ∀ {n : ℕ}, IsInt R (1 : Matrix (Fin n) (Fin n) K) := by
    intro n i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  rw [bigZ_conj,
    Fz_uni R Z' _ _ _ ((blkM_isLowUni rfl 1 0 0 v).2 ⟨isLowUni_one K, rfl, hv⟩)
      ((blkM_isInt rfl 1 0 0 v R).2 ⟨h1, fun i j => by simp, fun i j => by simp, hvi⟩)
      ((blkM_isUpUni rfl 1 0 0 u).2 ⟨isUpUni_one K, rfl, hu⟩)
      ((blkM_isInt rfl 1 0 0 u R).2 ⟨h1, fun i j => by simp, fun i j => by simp, hui⟩),
    cornL_low_mul hv, cornU_mul_up' hu]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
