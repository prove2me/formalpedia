-- Prove2me | solution 1 for Formalism.UnitaryBoundIntegral.ubint_mvExp_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:41.320297+00:00
-- url     : https://prove2.me/submissions/c2d52ded-388f-42f1-ac9a-7b7c3ff4e182

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Definitions.Def_Formalism_DropLevelBounds_ConstantCoeffVanishing_UbintConstantCoeffEqZero
import Theorems.Thm_Formalism_UnitaryBoundIntegral_ubint_mvExp_zero
import Theorems.Thm_Formalism_IncomingBounds_expSeriesAdd


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
open MvPowerSeries Finset
open Formalism Formalism.UnitaryBoundIntegral
open Formalism.IncomingBounds
variable {C : Type} [Field C] {σ : Type}
namespace Formalism.UnitaryBoundIntegral
theorem _root_.solution [CharZero C] {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ C)
    (hf : ∀ i ∈ s, constantCoeff (f i) = 0) :
    mvExp (∑ i ∈ s, f i) = ∏ i ∈ s, mvExp (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ubint_mvExp_zero]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, constantCoeff (f i) = 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h0 : constantCoeff (∑ i ∈ s, f i) = 0 := by
      rw [map_sum]
      exact Finset.sum_eq_zero hs
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      expSeriesAdd C σ (f a) _ (hf a (Finset.mem_insert_self a s)) h0, ih hs]
end Formalism.UnitaryBoundIntegral
