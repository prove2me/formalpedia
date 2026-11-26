-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.choose_two_sub_div_fixedSet_eq_separator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:29.777941+00:00
-- url     : https://prove2.me/submissions/d1aefe29-b28e-483b-9a4c-b45937ba413b

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N) :
    (((N - 2).choose (s - 2) : ℕ) : ℝ) /
        ((fixedSet N s).card : ℝ) =
      centralSeparatorProportion N s := by
  have hidentityNat :
      (N - 1) * (N - 2).choose (s - 2) =
        (N - 1).choose (s - 1) * (s - 1) := by
    simpa [show N - 2 + 1 = N - 1 by omega,
      show s - 2 + 1 = s - 1 by omega] using
      (Nat.add_one_mul_choose_eq (N - 2) (s - 2))
  have hidentity :
      (((N - 1 : ℕ) : ℝ)) * ((N - 2).choose (s - 2) : ℝ) =
        ((N - 1).choose (s - 1) : ℝ) * (((s - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hidentityNat
  have hchooseTotal :
      0 < (((N - 1).choose (s - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ N - 1)
  have hNm1 : 0 < (((N - 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.sub_pos_of_lt (by omega : 1 < N)
  rw [card_fixedSet N s (by omega) (by omega)]
  unfold centralSeparatorProportion
  apply (div_eq_div_iff (ne_of_gt hchooseTotal) (ne_of_gt hNm1)).2
  nlinarith [hidentity]
end CollatzEndpointTransport.FixedTotal
