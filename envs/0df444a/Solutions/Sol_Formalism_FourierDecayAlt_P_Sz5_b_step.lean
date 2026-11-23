-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz5.b_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:55.748261+00:00
-- url     : https://prove2.me/submissions/9fde6d2a-8125-4286-ae95-3048dae498a4

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz5
theorem _root_.solution (c : Cfg) (h : c.Ok) (i : ℕ) (hi : 1 ≤ i) :
    ∀ j, i < j → j ≤ c.m → c.b i + 1 ≤ c.b j := by
  intro j hij hjm
  induction j with
  | zero => omega
  | succ n ih =>
    by_cases hc : i < n
    · have h1 := ih hc (by omega)
      have h2 := h.hgap n (by omega) (by omega)
      linarith
    · have hin : i = n := by omega
      rw [← hin]
      exact h.hgap i hi (by omega)
end Formalism.FourierDecayAlt.P.Sz5
