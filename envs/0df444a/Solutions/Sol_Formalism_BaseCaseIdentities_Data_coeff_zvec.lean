-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_zvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:22.505407+00:00
-- url     : https://prove2.me/submissions/b9453592-bab6-4e22-a98f-63a670e46d36

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds

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
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (d : Z) (c : C) :
    coeff (Finsupp.single d 1) (D.zvec c) = if D.ι d = c then 1 else 0 := by
  unfold zvec
  rw [map_sum, Finset.sum_eq_single d]
  · split_ifs <;> simp [coeff_X]
  · intro e _ hne
    split_ifs
    · rw [coeff_X, if_neg]
      intro h
      exact hne ((Finsupp.single_left_inj one_ne_zero).1 h).symm
    · simp
  · simp
end Formalism.BaseCaseIdentities.Data
