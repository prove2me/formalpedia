-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.pairs_r
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:30.95581+00:00
-- url     : https://prove2.me/submissions/77d899ea-ab6b-44e5-a9a9-99f061649830

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqPairs
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_sP_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_RR_nonneg
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_pairs_r_prime
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_Pairs_pairs_r_not_prime

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
open Pairs
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N r : ℕ) (hr : 1 < r)
    (B : ℝ) (hB : ∀ p, sP c N p ≤ B) :
    (∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      2 * B ^ 2 + 2 * B * RR c m₀ N := by
  have hB0 : 0 ≤ B := le_trans (sP_nonneg hc N 0) (hB 0)
  have hR := RR_nonneg hc m₀ N
  by_cases hrp : r.Prime
  · refine le_trans (pairs_r_prime c hc hpp m₀ N r hrp) ?_
    have h1 := sP_nonneg hc N r
    have h2 := hB r
    nlinarith [mul_le_mul h2 h2 h1 hB0, mul_le_mul_of_nonneg_right h2 hR, mul_nonneg hB0 hB0]
  · refine le_trans (pairs_r_not_prime c hc hpp m₀ N r hr hrp) ?_
    have a1 := sP_nonneg hc N r.minFac
    have a2 := sP_nonneg hc N (r / r.minFac)
    have b1 := hB r.minFac
    have b2 := hB (r / r.minFac)
    nlinarith [mul_le_mul b1 b2 a2 hB0, mul_le_mul b2 b1 a1 hB0, mul_nonneg hB0 hR]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
