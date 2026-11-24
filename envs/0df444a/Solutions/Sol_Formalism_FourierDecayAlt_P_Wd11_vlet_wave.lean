-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.vlet_wave
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:49.301827+00:00
-- url     : https://prove2.me/submissions/f57d4473-44bd-4f2b-814f-d609669a9b16

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_letter_wave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (σ : Site A) (f fi : A) (s : K) (l : Letter K S)
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) :
    vlet σ l * (io f * ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) =
      io f * vlet σ l := by
  unfold vlet
  rw [← insL_diag l.intersection_update_fsHerm_neg_one f, ← insL_mul, ← insL_mul, ← insL_mul, ← mul_assoc,
    letter_wave σ f fi s l hW hc hci hp]
end Formalism.FourierDecayAlt.P.Wd11
