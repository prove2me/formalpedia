-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ordGE_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:53:45.144901+00:00
-- url     : https://prove2.me/submissions/0aa5a740-5011-4770-aeb4-0b5df9109011

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
theorem _root_.solution (f : MvPowerSeries τ C) : OrdGE 1 f ↔ constantCoeff f = 0 := by
  constructor
  · intro h
    have := h 0 (by simp)
    simpa using this
  · intro h A hA
    have hA0 : A = 0 := by
      have : A.degree = 0 := by omega
      exact (Finsupp.degree_eq_zero_iff A).1 this
    subst hA0
    simpa using h
end Formalism.L2.FormalSeriesBounds
