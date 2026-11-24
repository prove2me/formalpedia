-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs.pairs_r_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:38.52371+00:00
-- url     : https://prove2.me/submissions/41808ddf-5c2e-43fe-a046-5d83ce21c443

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_same
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_soutPart_diff
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_primePowerSum_eq_sum_Icc
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_aW_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_aW_self
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
    (hr : 1 < r) (hrp : ¬ r.Prime) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
  have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n' := by
    intro n n'
    have q1 := mul_nonneg (aW_nonneg hc r.minFac n) (aW_nonneg hc (r / r.minFac) n')
    have q2 := mul_nonneg (aW_nonneg hc (r / r.minFac) n) (aW_nonneg hc r.minFac n')
    split_ifs with hs
    swap
    · linarith
    by_cases hcn : c n = 0
    · rw [hcn, zero_mul]; linarith
    by_cases hcn' : c n' = 0
    · rw [hcn', mul_zero]; linarith
    have hn := hpp n hcn
    have hn' := hpp n' hcn'
    have p1 := Nat.minFac_prime hn.ne_one
    have p2 := Nat.minFac_prime hn'.ne_one
    by_cases he : n.minFac = n'.minFac
    · exfalso
      rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
      · exact hr.ne' (hs.symm.trans h1)
      · exact hrp (by rw [← hs, h1]; exact p1)
    · have hd := soutPart_diff (m₀ := m₀) hn hn' he
      rw [hs] at hd
      rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
        rw [t1, t2] at hd
      · exact absurd (hd.trans (one_mul 1)) hr.ne'
      · exact absurd (by rw [hd, one_mul]; exact p2) hrp
      · exact absurd (by rw [hd, mul_one]; exact p1) hrp
      · have hmf : r.minFac = n.minFac ∨ r.minFac = n'.minFac := by
          have hpr := Nat.minFac_prime (show r ≠ 1 by omega)
          have hdvd : r.minFac ∣ n.minFac * n'.minFac := by rw [← hd]; exact Nat.minFac_dvd r
          rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpr p1).1 h)
          · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpr p2).1 h)
        have ha : aW c n.minFac n = c n := aW_self hn
        have hb : aW c n'.minFac n' = c n' := aW_self hn'
        rcases hmf with h | h
        · have hq : r / r.minFac = n'.minFac := by rw [h, hd, Nat.mul_div_cancel_left _ p1.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
        · have hq : r / r.minFac = n.minFac := by rw [h, hd, Nat.mul_div_cancel _ p2.pos]
          rw [hq, h, ha, hb]
          have := mul_nonneg (aW_nonneg hc n'.minFac n) (aW_nonneg hc n.minFac n')
          linarith
  calc (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0)
      ≤ ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N,
          (aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n') :=
        Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun n' _ => hpt n n'))
    _ = sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
        simp only [Finset.sum_add_distrib, dbl_sum, primePowerSum_eq_sum_Icc]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.Pairs
