-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.hasUniqueFixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:15.565936+00:00
-- url     : https://prove2.me/submissions/9e277795-93fb-4519-afc7-b42cc52acf52

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_eq_of_ordGE
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_iterate_close
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_fixPt
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_Psi_fixPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.FixedPoint := by
  refine ⟨⟨D.fixPt, ⟨D.noConst_fixPt, D.Psi_fixPt⟩, ?_⟩, ?_⟩
  · rintro y ⟨hy, hy'⟩
    funext c
    apply eq_of_ordGE
    intro n
    have h := D.iterate_close hy D.noConst_fixPt n c
    rwa [Function.iterate_fixed hy', Function.iterate_fixed D.Psi_fixPt] at h
  · intro t0 t ht0 ht hfix n A hA c
    have h := D.iterate_close ht0 ht n c A (by omega)
    rw [map_sub, sub_eq_zero, Function.iterate_fixed hfix] at h
    exact h
end Formalism.BaseCaseIdentities.Data
