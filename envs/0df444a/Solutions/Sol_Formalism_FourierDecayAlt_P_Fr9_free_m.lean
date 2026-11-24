-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.free_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:42:52.376802+00:00
-- url     : https://prove2.me/submissions/e08cf881-5855-4faf-852f-1bfe195cc9f9

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_free_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_free_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {b : S}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (hf : f.Free b) (Y : ℂ) : FreeOf b (f.m L Y) :=
  Wd11.free_mul (Wd11.free_mul (Wd11.free_mul hf.2.2.2.2.2.2.2.1 (free_pow (Wd11.free_io b _) _))
    (free_star (free_l hf _))) (Wd11.free_mul (free_pow (Wd11.free_io b _) _) hf.2.2.2.2.2.2.1)
end Formalism.FourierDecayAlt.P.Fr9
