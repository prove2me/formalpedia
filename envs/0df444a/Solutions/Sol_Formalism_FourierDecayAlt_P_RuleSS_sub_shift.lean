-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.sub_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:46:52.063447+00:00
-- url     : https://prove2.me/submissions/5f578ce4-63a4-4763-be9b-25a888260cac

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {x h : A} {s : ℂ} (hx : x * h = h * (x + algebraMap ℂ A s)) (Y Y' : ℂ)
    (hY : Y' = Y - s) : (algebraMap ℂ A Y - x) * h = h * (algebraMap ℂ A Y' - x) := by
  rw [sub_mul, hx, Algebra.commutes Y h, hY, map_sub]; noncomm_ring
end Formalism.FourierDecayAlt.P.RuleSS
