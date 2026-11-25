-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.low_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:31.3908+00:00
-- url     : https://prove2.me/submissions/2b62fbbe-49ac-46c5-8aa2-e9980b2de3c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_pow

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
theorem _root_.solution {E : ℕ} {t : σ → MvPowerSeries σ C} (ht : ∀ s, OrdV 1 (t s))
    (ht' : ∀ s, LowLt (v := v) (E + 1) (t s)) (S : Finset σ) (d : σ → ℕ) :
    OrdV (∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) ∧ LowLt (v := v) (E + ∑ s ∈ S, d s) (∏ s ∈ S, t s ^ d s) := by
  refine Finset.induction_on S ?_ ?_
  · rw [Finset.sum_empty, Finset.prod_empty, Nat.add_zero]
    exact low_one E
  · intro a S ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hp := low_pow (ht a) (ht' a) (d a)
    rw [Nat.mul_one] at hp
    exact low_mul hp.1 hp.2 ih.1 ih.2
end Formalism.L2.FormalSeriesBounds.AltInv
