-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.low_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:06.091231+00:00
-- url     : https://prove2.me/submissions/660bad9f-4d2d-4e96-90e0-437674cc5f01

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
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
theorem _root_.solution (E : ℕ) : OrdV 0 (1 : MvPowerSeries σ C) ∧ LowLt (v := v) E (1 : MvPowerSeries σ C) :=
  ⟨fun _ hμ => absurd hμ (Nat.not_lt_zero _), fun μ _ => intS_one μ⟩
end Formalism.L2.FormalSeriesBounds.AltInv
