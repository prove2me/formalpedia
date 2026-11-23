-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.outM_clsM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:02.798939+00:00
-- url     : https://prove2.me/submissions/36e8c943-e1ce-4a54-86ad-c1d7fa07430d

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_clsM_outM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_clsM_eq
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
theorem _root_.solution {ι κ : Type} (x : Matrix ι κ K) (i : ι) (j : κ) :
    (outM R (clsM R x) - x) i j ∈ R := by
  exact (clsM_eq R (outM R (clsM R x)) x).1 (clsM_outM R (clsM R x)) i j
end Formalism.FourierDecayAlt.P.TwoBlockPoint
