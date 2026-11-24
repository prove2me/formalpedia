-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.freeOf2_rmatrix_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:31.468743+00:00
-- url     : https://prove2.me/submissions/8072c583-8085-4cca-843e-5ed7847e6620

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_freeOf2_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution {a c : S} (hc : c ≠ a) (d : K) : FreeOf2 c (Rht0 a d : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  simp only [Rht0, Matrix.smul_apply, Matrix.sub_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc i j))
end Formalism.FourierDecayAlt.P.Wd5
