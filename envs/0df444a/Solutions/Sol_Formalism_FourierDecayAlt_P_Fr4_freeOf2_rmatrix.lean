-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.freeOf2_rmatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:50.631823+00:00
-- url     : https://prove2.me/submissions/cb468768-6545-4b5e-956f-c6cbc36e26c8

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_free_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr4_freeOf2_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution {a c : S} (hc : c ≠ a) (D : ℂ) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  unfold Rh0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact free_smul _ (free_sub (free_smul _ (freeOf2_one c i j)) (free_eU hc j i))
end Formalism.FourierDecayAlt.P.Fr4
