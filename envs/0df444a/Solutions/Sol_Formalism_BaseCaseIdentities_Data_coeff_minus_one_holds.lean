-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.coeff_minus_one_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:02:53.427228+00:00
-- url     : https://prove2.me/submissions/f3557ea5-1fec-40f7-8f56-fae8e73f1e40

import Definitions.Def_Formalism_FrobeniusBaseCase_CoeffOfFirstMultiplier
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_SecondWayHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_zvec
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_m_succ
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_q_pos
import Theorems.Thm_Formalism_BaseCaseIdentities_coeff_frob_smul


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
theorem _root_.solution : D.CoeffOfFirstMultiplier := by
  intro d b
  rw [m_succ, coeff_C_mul, map_sum]
  congr 1
  rw [Finset.sum_eq_single (D.ι d)]
  · rw [coeff_mul_C, coeff_frob_smul _ D.q_pos]
    show (coeff (Finsupp.single d 1) (D.zvec (D.ι d))) ^ D.q * _ = _
    rw [coeff_zvec, if_pos rfl, one_pow, one_mul]
  · intro c _ hne
    rw [coeff_mul_C, coeff_frob_smul _ D.q_pos]
    show (coeff (Finsupp.single d 1) (D.zvec c)) ^ D.q * _ = _
    rw [coeff_zvec, if_neg (fun h => hne h.symm), zero_pow (by have := D.q_pos; omega), zero_mul]
  · simp
end Formalism.BaseCaseIdentities.Data
