-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminal_choose_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:26.581796+00:00
-- url     : https://prove2.me/submissions/003f9b49-a620-4005-83f8-f20edc842014

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_div_succ_le_binomial_mass_at_mean
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomial_term_le_one
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
    {n k D r : ℕ}
    (hn : 0 < n) (hk0 : 0 < k) (hkn : k < n)
    (hrk : r ≤ k) (hrD : r ≤ D)
    (hDr : D - r ≤ n - k) :
    ((n - D).choose (k - r) : ℝ) / (n.choose k : ℝ) ≤
      (n + 1 : ℝ) *
        ((k : ℝ) / n) ^ r *
        (((n - k : ℕ) : ℝ) / n) ^ (D - r) := by
  have hDn : D ≤ n := by omega
  have hres : k - r ≤ n - D := by omega
  let p : ℝ := (k : ℝ) / n
  let q : ℝ := ((n - k : ℕ) : ℝ) / n
  let base : ℝ := p ^ (k - r) * q ^ ((n - D) - (k - r))
  let pat : ℝ := p ^ r * q ^ (D - r)
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by
    dsimp [q]
    have : 0 < n - k := Nat.sub_pos_of_lt hkn
    positivity
  have hpq : p + q = 1 := by
    dsimp [p, q]
    rw [Nat.cast_sub hkn.le]
    field_simp
    ring
  have hbase : 0 < base := by dsimp [base]; positivity
  have hpat : 0 ≤ pat := by dsimp [pat]; positivity
  have hresMass : ((n - D).choose (k - r) : ℝ) * base ≤ 1 := by
    simpa [base, mul_assoc] using
      binomial_term_le_one hres hp.le hq.le hpq
  have hdenMass :
      (1 : ℝ) / (n + 1) ≤
        (n.choose k : ℝ) * p ^ k * q ^ (n - k) := by
    simpa [p, q] using
      one_div_succ_le_binomial_mass_at_mean hn hkn.le
  have hpowP : p ^ k = p ^ (k - r) * p ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hrk]
  have hpowQ :
      q ^ (n - k) =
        q ^ ((n - D) - (k - r)) * q ^ (D - r) := by
    rw [← pow_add]
    congr 1
    omega
  have hdenOne :
      1 ≤ (n + 1 : ℝ) * (n.choose k : ℝ) * base * pat := by
    have h := (div_le_iff₀ (show (0 : ℝ) < n + 1 by positivity)).mp hdenMass
    dsimp [base, pat]
    rw [hpowP, hpowQ] at h
    nlinarith
  have hcross :
      ((n - D).choose (k - r) : ℝ) * base ≤
        ((n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ)) * base := by
    calc
      ((n - D).choose (k - r) : ℝ) * base ≤ 1 := hresMass
      _ ≤ (n + 1 : ℝ) * (n.choose k : ℝ) * base * pat := hdenOne
      _ = ((n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ)) * base := by
            dsimp [pat]
            ring
  have hnum :
      ((n - D).choose (k - r) : ℝ) ≤
        (n + 1 : ℝ) * p ^ r * q ^ (D - r) *
          (n.choose k : ℝ) := by
    exact (mul_le_mul_iff_of_pos_right hbase).mp hcross
  have hchoose : 0 < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hkn.le
  apply (div_le_iff₀ hchoose).2
  simpa [p, q, mul_assoc] using hnum
end CollatzEndpointTransport.FixedTotal
