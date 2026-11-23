-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx1.euler_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:06.657694+00:00
-- url     : https://prove2.me/submissions/3504b3e7-39c4-4795-8f78-43aa3671316e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx1
namespace Formalism.FourierDecayAlt.P.Mx1
theorem _root_.solution {r : ℕ} (v : Var r) (f : Fn r) : (euler v f).support ⊆ f.support := by
  intro γ hγ
  rw [HahnSeries.mem_support] at hγ ⊢
  intro h
  apply hγ
  show ((ofLex γ v : ℤ) : ℂ) * f.coeff γ = 0
  rw [h, mul_zero]
end Formalism.FourierDecayAlt.P.Mx1
