-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.noConst_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:57:02.482799+00:00
-- url     : https://prove2.me/submissions/7b994490-24ce-4dd8-a3ed-9e97eb16c6d4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero

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
variable {k : Type*} [Field k] {Z B : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (t : B → MvPowerSeries Z k) :
    NoConst t ↔ ∀ c, MvPowerSeries.constantCoeff (t c) = 0 := by
  constructor
  · intro h c
    have h0 := h c 0 (by simp)
    simpa using h0
  · intro h c A hA
    have hA0 : A.degree = 0 := by omega
    have hA1 : A = 0 := by
      first
      | exact (Finsupp.degree_eq_zero_iff A).mp hA0
      | exact Finsupp.degree_eq_zero_iff.mp hA0
      | simpa using hA0
    subst hA1
    simpa using h c
end Formalism.L2.FormalSeriesBounds
