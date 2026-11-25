-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:11.221737+00:00
-- url     : https://prove2.me/submissions/439148cb-e7fe-4e1d-8925-297a5d59413d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_one

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS v (f i)) :
    IntS v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntS v) (fun _ _ => intS_mul) intS_one h
end Formalism.L2.FormalSeriesBounds.AltInv
