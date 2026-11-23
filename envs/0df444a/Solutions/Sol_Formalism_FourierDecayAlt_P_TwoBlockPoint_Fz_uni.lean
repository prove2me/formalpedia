-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.Fz_uni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:18.671361+00:00
-- url     : https://prove2.me/submissions/bc9edcc7-3520-4da8-8640-99ae080dc365

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_intInv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_eZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_intInv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_mul
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_card_isoZZ_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_isoZZ_refl
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x4_lamLin_mk_eq
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
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {n n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (a0 b0 Z : Matrix (Fin n) (Fin n) K)
    (haL : IsLowUni a0) (haI : IsInt R a0) (hbU : IsUpUni b0) (hbI : IsInt R b0) :
    Fz R Z' (a0 * Z * b0) = Fz R Z' Z := by
  have hint := Formalism.DoubleCosetMeasures.P.intInv K R n a0 b0 Z haL hbU haI hbI
  have hiso : ∃ φ : coker R Z ≃ₗ[R] coker R (a0 * Z * b0), φ ∈ isoZZ R Z (a0 * Z * b0) := by
    obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin n) (Fin n) R, A.map R.subtype = a0 :=
      ⟨Formalism.DoubleCosetMeasures.P.liftR R a0 haI, Formalism.DoubleCosetMeasures.P.liftR_map R a0 haI⟩
    obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin n) (Fin n) R, B.map R.subtype = b0 :=
      ⟨Formalism.DoubleCosetMeasures.P.liftR R b0 hbI, Formalism.DoubleCosetMeasures.P.liftR_map R b0 hbI⟩
    have hA := isLowUni_det K haL
    have hB := isUpUni_det K hbU
    refine ⟨Formalism.DoubleCosetMeasures.P.cokEquiv R A B Z hA hB, Formalism.DoubleCosetMeasures.P.cokEquiv_eZ R A B Z hA hB haL,
      fun v v' hv => ?_⟩
    rw [Formalism.DoubleCosetMeasures.P.cokEquiv_mk] at hv
    rw [← Formalism.FourierDecayAlt.P.A5x4.lamLin_mk_eq R _ hv, Formalism.DoubleCosetMeasures.P.lamLin_mul R A B Z hA hbU]
  obtain ⟨φ, hφ⟩ := hiso
  unfold Fz
  rw [← Formalism.FourierDecayAlt.P.A5x4.card_isoZZ_congr R hφ (Formalism.FourierDecayAlt.P.A5x4.isoZZ_refl R Z')]
  by_cases hc : IsInt R Z
  · rw [if_pos hc, if_pos (hint.2 hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hint.1 h))]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
