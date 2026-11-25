-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.blkM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:40:31.818802+00:00
-- url     : https://prove2.me/submissions/19b60b5e-a08f-4246-9ab4-ab76f4cc7401

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
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
variable {K : Type} [CommRing K] {a s N : ℕ}
variable (hN : N = a + s) (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin a) (Fin s) K)
    (C C' : Matrix (Fin s) (Fin a) K) (D D' : Matrix (Fin s) (Fin s) K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution : blkM hN (1 : Matrix (Fin a) (Fin a) K) 0 0 1 = 1 := by
  unfold blkM
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
