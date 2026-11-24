-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Contr.exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:12:07.297407+00:00
-- url     : https://prove2.me/submissions/604b16f9-7b14-4551-8cdb-1525694f78f7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_iterate_close
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_noConst_fixPt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Contr_fix_fixPt
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_iterate_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_fixPt


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
theorem _root_.solution : ∃! t : B → MvPowerSeries Z k, NoConst t ∧ Ψ t = t := by
  refine ⟨H.fixPt, ⟨H.noConst_fixPt, H.fix_fixPt⟩, ?_⟩
  rintro t ⟨ht, hft⟩
  funext c
  ext A
  have h1 := H.iterate_close ht H.noConst_fixPt A.degree c A (Nat.lt_succ_self _)
  rw [Function.iterate_fixed hft, Function.iterate_fixed H.fix_fixPt, map_sub, sub_eq_zero] at h1
  exact h1
end Formalism.L2.FormalSeriesBounds.Contr
