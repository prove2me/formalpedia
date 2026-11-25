-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.arithmetic_reflected_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:28:59.949491+00:00
-- url     : https://prove2.me/submissions/253f6c06-00ee-4be7-8b6d-428a9ff7fec8

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_card_filter_Ico_eq_sub
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_sum_split_three_intervals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : WEArithReflected := by
  intro k j t q l h κ mw mwp U U' kc kp _ _ hU hU' hsum hminor hkc hkp
  have sU := sum_split_three_intervals U (k + j) (k + j + t) (by omega)
  have sU' := sum_split_three_intervals U' t (k + j + t) (by omega)
  have c1 : (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < t)).card = t := by
    have := card_filter_Ico_eq_sub (k + j + t + q) 0 t (by omega)
    simpa using this
  have c2 : (univ.filter
      (fun a : Fin (k + j + t + q) => k + j ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t)).card = t := by
    have := card_filter_Ico_eq_sub (k + j + t + q) (k + j) (k + j + t) (by omega)
    omega
  have c3 : (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j)).card = k + j := by
    have := card_filter_Ico_eq_sub (k + j + t + q) 0 (k + j) (by omega)
    simpa using this
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, c1, c2]
    at hminor
  have hmid : 0 ≤ ∑ a ∈ univ.filter
      (fun a : Fin (k + j + t + q) => t ≤ (a : ℕ) ∧ (a : ℕ) < k + j + t), U' a :=
    Finset.sum_nonneg (fun a _ => hU' a)
  have htop : ∑ a ∈ univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j), U a ≤
      ((k : ℤ) + j) * h := by
    calc _ ≤ (univ.filter (fun a : Fin (k + j + t + q) => (a : ℕ) < k + j)).card • (h : ℤ) :=
          Finset.sum_le_card_nsmul _ _ _ (fun a _ => hU a)
      _ = ((k : ℤ) + j) * h := by rw [c3, nsmul_eq_mul]; push_cast; ring
  have hkp' : (l : ℤ) * kp ≤ (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self kp) hkp) (Int.natCast_nonneg l)
  have hkc' : -kc ≤ (mw : ℤ) * ((t : ℤ) + 2 * κ) := le_trans (neg_le_abs kc) hkc
  have e : ((l : ℤ) * mwp + mw) * ((t : ℤ) + 2 * κ) =
      (l : ℤ) * ((mwp : ℤ) * ((t : ℤ) + 2 * κ)) + (mw : ℤ) * ((t : ℤ) + 2 * κ) := by ring
  rw [Finset.sum_sub_distrib, e]
  linarith
end Formalism.CohomologicalDescent.WorkedExample
