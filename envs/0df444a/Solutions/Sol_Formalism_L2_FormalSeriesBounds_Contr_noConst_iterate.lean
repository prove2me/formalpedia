-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.noConst_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:40.435219+00:00
-- url     : https://prove2.me/submissions/79d7460c-7404-4b2e-a7d2-15f22f95ccc4

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
open Formalism.L2.FormalSeriesBounds.Contr
variable {Ψ : (B → MvPowerSeries Z k) → (B → MvPowerSeries Z k)} (H : Contr Ψ)
include H
namespace Formalism.L2.FormalSeriesBounds.Contr
theorem _root_.solution {t : B → MvPowerSeries Z k} (ht : NoConst t) (n : ℕ) :
    NoConst (Ψ^[n] t) := by
  cases n with
  | zero => simpa using ht
  | succ n =>
    rw [Function.iterate_succ_apply']
    exact H.noConst _
end Formalism.L2.FormalSeriesBounds.Contr
