-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.entry_commute_R_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:58.199739+00:00
-- url     : https://prove2.me/submissions/64e68c01-eb09-4421-9f79-1c5b6856732b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_EC_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {z : SlopeTestRemainingChoices S A} {a : S} (h : ∀ i j, Commute z (eU a i j)) (D : K) : EC z (Rh0 a D) := by
  intro i j
  unfold Rh0 P0
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.of_apply]
  exact Commute.smul_right (Commute.sub_right (Commute.smul_right (EC.one z i j) _) (h j i)) _
end Formalism.FourierDecayAlt.P.Wd6
