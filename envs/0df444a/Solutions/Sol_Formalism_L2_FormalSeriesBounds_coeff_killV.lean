-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_killV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:11.772257+00:00
-- url     : https://prove2.me/submissions/07f0136f-ef1a-4964-bf81-43f53745f8d6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (P : σ → Prop) (F : MvPowerSeries σ C) (μ : σ →₀ ℕ) :
    coeff μ (killV P F) = if ∀ w ∈ μ.support, P w then coeff μ F else 0 := rfl
end Formalism.L2.FormalSeriesBounds
