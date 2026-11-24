-- Prove2me | solution 1 for Formalism.FG.FunctionalEquationHom.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:12:09.545418+00:00
-- url     : https://prove2.me/submissions/285fa8ff-4827-4c1c-b86a-222b3db2d3ad

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationSubstVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Theorems.Thm_Formalism_FG_FunctionalEquationHom_funEqV_sub
import Theorems.Thm_Formalism_FG_FunctionalEquationHom_two_le_q

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.FunctionalEquationHom
open Formalism.G Formalism.LT
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.FG.FunctionalEquationHom
theorem _root_.solution (hSol : Formalism.FG.SolveExistsV.{u, v, w}) (hInv : Formalism.FG.InvIntegralV.{u, v, w})
    (hLow : Formalism.FG.LowCoeffV.{u, v, w}) (hKey : Formalism.FG.FunEqSubstV.{u, v, w}) :
    Formalism.FG.FunEqHomV.{u, v, w} := by
  intro K _ _ _ p q hq σ hS ι _ _ M hM f hf hfF τ _ g hg0 hgF
  obtain ⟨h, h0, hsub⟩ := hSol K ι τ f g hf hg0
  refine ⟨h, h0, ?_, hsub⟩
  have hC : IsFunEqTypeV p q hq σ M (fun j => MvPowerSeries.subst h (f j)) := by
    have e : (fun j => MvPowerSeries.subst h (f j)) = g := funext hsub
    rw [e]
    exact hgF
  exact hInv K ι τ (IsFunEqTypeV p q hq σ M) f hf
    (fun a b ha hb => funEqV_sub hq σ M ha hb)
    (fun P hP0 hPI => hKey K p q hq σ hS ι M hM f hf.1 hfF τ P hP0 hPI)
    (fun D hD N hN hlow => hLow K p q hq σ (two_le_q hS) ι M τ D hD N hN hlow)
    h h0 hC
end Formalism.FG.FunctionalEquationHom
