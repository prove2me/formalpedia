-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.iterate_close
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:33.818188+00:00
-- url     : https://prove2.me/submissions/2269d660-a7ea-4bbe-9962-21817b269508

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_iterate
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_iterate
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
theorem _root_.solution {a b : B → MvPowerSeries Z k} (ha : NoConst a) (hb : NoConst b) (n : ℕ) :
    ∀ c, OrdGE (n + 1) (Ψ^[n] a c - Ψ^[n] b c) := by
  induction n with
  | zero =>
    intro c A hA
    simp only [Function.iterate_zero, id_eq, map_sub, ha c A hA, hb c A hA, sub_zero]
  | succ n ih =>
    intro c
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact H.contr _ _ n (H.noConst_iterate ha n) (H.noConst_iterate hb n) ih c
end Formalism.L2.FormalSeriesBounds.Contr
