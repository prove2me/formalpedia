-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.freeOf2_rmatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:10.197045+00:00
-- url     : https://prove2.me/submissions/52c85543-3d00-417c-938b-35fc41f139ad

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_freeOf2_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution {a c : S} (hc : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  have h : (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j =
      (D - 1)⁻¹ • (D • (1 : M2 (SlopeTestRemainingChoices S A)) i j - eU a j i) := rfl
  rw [h]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))
end Formalism.FourierDecayAlt.P.Wd7
