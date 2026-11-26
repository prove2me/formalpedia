-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.one_div_succ_le_binomial_mass_at_mean
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:17.274796+00:00
-- url     : https://prove2.me/submissions/ac139752-2872-4765-a2ca-b19685433d21

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_pow_le_succ_mul_scaledBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    (1 : ℝ) / (n + 1) ≤
      (n.choose k : ℝ) *
        ((k : ℝ) / n) ^ k *
        (((n - k : ℕ) : ℝ) / n) ^ (n - k) := by
  have hpow : 0 < (n : ℝ) ^ n := by positivity
  have hscaled := pow_le_succ_mul_scaledBinomialMass hk
  have heq :
      (n.choose k : ℝ) *
          ((k : ℝ) / n) ^ k *
          (((n - k : ℕ) : ℝ) / n) ^ (n - k) =
        (scaledBinomialMass n k k : ℝ) / (n : ℝ) ^ n := by
    rw [div_pow, div_pow]
    field_simp [show (n : ℝ) ≠ 0 by positivity]
    unfold scaledBinomialMass
    push_cast
    rw [Nat.cast_sub hk]
    rw [← pow_add, Nat.add_sub_of_le hk]
    ring
  rw [heq]
  apply (div_le_div_iff₀
    (show (0 : ℝ) < n + 1 by positivity) hpow).2
  norm_num
  have hscaledR :
      ((n ^ n : ℕ) : ℝ) ≤
        (((n + 1) * scaledBinomialMass n k k : ℕ) : ℝ) := by
    exact_mod_cast hscaled
  norm_num at hscaledR
  simpa [mul_comm] using hscaledR
end CollatzEndpointTransport.FixedTotal
