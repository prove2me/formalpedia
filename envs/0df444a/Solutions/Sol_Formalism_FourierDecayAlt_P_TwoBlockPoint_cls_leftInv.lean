-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.cls_leftInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:20.824881+00:00
-- url     : https://prove2.me/submissions/70795e1e-f8b1-45bb-8ac2-62734af9de43

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_clsM_outM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_clsM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_outM_clsM
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
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {ι κ : Type} (L L' : Matrix ι κ K → Matrix ι κ K)
    (hadd : ∀ U V, L' (U + V) = L' U + L' V)
    (hint : ∀ V, (∀ i j, V i j ∈ R) → ∀ i j, L' V i j ∈ R) (hinv : ∀ U, L' (L U) = U)
    (x : Matrix ι κ (KR R)) : clsM R (L' (outM R (clsM R (L (outM R x))))) = x := by
  rw [show outM R (clsM R (L (outM R x))) =
      L (outM R x) + (outM R (clsM R (L (outM R x))) - L (outM R x)) by abel, hadd, hinv]
  conv_rhs => rw [← clsM_outM R x]
  rw [clsM_eq]
  intro i j
  have := hint _ (outM_clsM R (L (outM R x))) i j
  simpa [Matrix.add_apply, Matrix.sub_apply] using this
end Formalism.FourierDecayAlt.P.TwoBlockPoint
