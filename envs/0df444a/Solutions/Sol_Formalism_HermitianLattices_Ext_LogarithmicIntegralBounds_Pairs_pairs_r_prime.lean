-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.pairs_r_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:38.667132+00:00
-- url     : https://prove2.me/submissions/428c38dc-7c5c-4d80-96c4-0f7932ca4f9e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_same
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_diff
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePowerSum_eq_sum_Icc
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_RR_eq
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_aW_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_gW_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_gW_eq_of_tPart_eq_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_tPart_cases
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_dbl_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
theorem _root_.solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ)
    (hr : r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r n) (aW_nonneg hc r n')
    have q2 := mul_nonneg (aW_nonneg hc r n) (gW_nonneg hc m₀ n')
    have q3 := mul_nonneg (gW_nonneg hc m₀ n) (aW_nonneg hc r n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    by_cases he : n.minFac = n'.minFac
    · rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact absurd (hs.symm.trans h1) hr.one_lt.ne'
      · have hnr : n.minFac = r := h1.symm.trans hs
        have hnr' : n'.minFac = r := he.symm.trans hnr
        have e1 : aW c r n = c n := by unfold aW; rw [if_pos ⟨hn, hnr⟩]
        have e2 : aW c r n' = c n' := by unfold aW; rw [if_pos ⟨hn', hnr'⟩]
        rw [e1, e2]
        have := mul_nonneg (hc n) (gW_nonneg hc m₀ n')
        have := mul_nonneg (gW_nonneg hc m₀ n) (hc n')
        linarith
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      have p1 := Nat.minFac_prime hn.ne_one
      have p2 := Nat.minFac_prime hn'.ne_one
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.one_lt.ne'
      · have e1 : gW c m₀ n = c n := gW_eq_of_tPart_eq_one hn t1
        have e2 : aW c r n' = c n' := by
          unfold aW; rw [if_pos ⟨hn', by rw [hd, one_mul]⟩]
        rw [e1, e2]
        have := mul_nonneg (aW_nonneg hc r n) (hc n')
        linarith
      · have e1 : aW c r n = c n := by
          unfold aW; rw [if_pos ⟨hn, by rw [hd, mul_one]⟩]
        have e2 : gW c m₀ n' = c n' := gW_eq_of_tPart_eq_one hn' t2
        rw [e1, e2]
        have := mul_nonneg (hc n) (aW_nonneg hc r n')
        linarith
      · exfalso
        rw [hd] at hr
        rcases Nat.prime_mul_iff.1 hr with ⟨-, h⟩ | ⟨-, h⟩
        · exact p2.one_lt.ne' h
        · exact p1.one_lt.ne' h
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc, RR_eq]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
