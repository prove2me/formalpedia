-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Top.lemma4Geom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:55.040219+00:00
-- url     : https://prove2.me/submissions/4a5b0389-d9aa-4886-b48d-7d971fab89e7

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ExistsNonzeroExchangedMinorHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FrobeniusDetVanishingHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds
import Definitions.Def_Formalism_PolynomialDimension_DetMulEqSumAdjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.Top
namespace Formalism.CountingSumsFrames.Top
theorem _root_.solution : Formalism.CountingSumsFrames.Lemma4Geom := by
  intro p a B D0 S d hp ha hB hS
  have hp0 : 0 < p := by linarith
  have hp2 : 168 ≤ p ^ 2 - 1 := by nlinarith
  have hB0 : 0 ≤ B := le_trans (by positivity) hB
  have hx0 : 0 ≤ 1 / p ^ 2 := by positivity
  have hx1 : 1 / p ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  have hterm : ∀ m ∈ S, d m ≤ 2.02 * B * (1 / p ^ 2) ^ m := by
    intro m hm
    obtain ⟨_, _, hdm⟩ := hS m hm
    calc d m ≤ 2.02 * a / p ^ (D0 + 2 * m) := hdm
      _ = 2.02 * (a / p ^ D0) * (1 / p ^ 2) ^ m := by
          rw [pow_add, pow_mul, one_div_pow]
          ring
      _ ≤ 2.02 * B * (1 / p ^ 2) ^ m := by gcongr
  have h0S : 0 ∉ S := fun h => by have := (hS 0 h).1; omega
  have hgeom : ∑ m ∈ S, (1 / p ^ 2) ^ m ≤ 1 / (p ^ 2 - 1) := by
    have hsum := summable_geometric_of_lt_one hx0 hx1
    have h1 : ∑ m ∈ insert 0 S, (1 / p ^ 2) ^ m ≤ ∑' m : ℕ, (1 / p ^ 2) ^ m := by
      first
        | exact hsum.sum_le_tsum _ (fun m _ => pow_nonneg hx0 m)
        | exact sum_le_tsum _ (fun m _ => pow_nonneg hx0 m) hsum
    rw [Finset.sum_insert h0S, pow_zero, tsum_geometric_of_lt_one hx0 hx1] at h1
    have h2 : (1 - 1 / p ^ 2)⁻¹ - 1 = 1 / (p ^ 2 - 1) := by
      have hp2' : p ^ 2 - 1 ≠ 0 := by linarith
      have hp2'' : p ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    linarith
  refine ⟨?_, ?_⟩
  · calc ∑ m ∈ S, d m ≤ ∑ m ∈ S, 2.02 * B * (1 / p ^ 2) ^ m := Finset.sum_le_sum hterm
      _ = 2.02 * B * ∑ m ∈ S, (1 / p ^ 2) ^ m := by rw [Finset.mul_sum]
      _ ≤ 2.02 * B * (1 / (p ^ 2 - 1)) := by gcongr
      _ = 2.02 * B / (p ^ 2 - 1) := by ring
  · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
end Formalism.CountingSumsFrames.Top
