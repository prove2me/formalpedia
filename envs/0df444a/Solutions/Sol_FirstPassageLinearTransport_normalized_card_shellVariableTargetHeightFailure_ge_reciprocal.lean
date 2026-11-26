-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:06.299041+00:00
-- url     : https://prove2.me/submissions/a79594e6-84dd-4e6f-a82c-4794ca77f8e7

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Theorems.Thm_FirstPassageLinearTransport_shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellTargetHeightFailure_ge_reciprocal


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ, n ∈ dyadicShell M → u n ≤ U) :
    (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellVariableTargetHeightFailure M f u).card : ℝ) /
        (2 : ℝ) ^ M := by
  have hconstant := normalized_card_shellTargetHeightFailure_ge_reciprocal
    hhM hh hU hlog htarget
  have hcardNat := Finset.card_le_card
    (shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
      (f := f) hu)
  have hcard :
      ((shellTargetHeightFailure M f U).card : ℝ) ≤
        (shellVariableTargetHeightFailure M f u).card := by
    exact_mod_cast hcardNat
  exact hconstant.trans
    (div_le_div_of_nonneg_right hcard (by positivity))
end FirstPassageLinearTransport
