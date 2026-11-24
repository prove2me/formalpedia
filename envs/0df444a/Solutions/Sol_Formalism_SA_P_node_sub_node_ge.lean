-- Prove2me | solution 1 for Formalism.SA.P.node_sub_node_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:36:36.129748+00:00
-- url     : https://prove2.me/submissions/f4d551ed-1f3c-4327-a81f-77cb62e3e877

import Definitions.Def_Formalism_LatticeRigidity_StatementC
import Mathlib
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Finset Real Polynomial Polynomial.Chebyshev
namespace Formalism.SA.P
theorem _root_.solution {n i k : ℕ} (hn : 1 ≤ n) (hik : i < k) (hk : k ≤ n) :
    2 * ((k:ℝ) - i) ^ 2 / (n:ℝ) ^ 2 ≤ node n i - node n k := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hik' : (i:ℝ) < k := by exact_mod_cast hik
  have hkn : (k:ℝ) ≤ n := by exact_mod_cast hk
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
  have hpi := Real.pi_pos
  set S := ((i:ℝ) + k) * π / (2 * n) with hS
  set D := ((k:ℝ) - i) * π / (2 * n) with hD
  have hcos : node n i - node n k = 2 * sin S * sin D := by
    unfold node
    rw [Real.cos_sub_cos]
    have h1 : ((i:ℝ) * π / n + (k:ℝ) * π / n) / 2 = S := by
      rw [hS]; field_simp; try ring
    have h2 : ((i:ℝ) * π / n - (k:ℝ) * π / n) / 2 = -D := by
      rw [hD]; field_simp; try ring
    rw [h1, h2, Real.sin_neg]; ring
  have h2n : (0:ℝ) < 2 * n := by positivity
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg (by linarith) hpi.le) h2n.le
  have hDle : D ≤ π / 2 := by
    rw [hD, div_le_iff₀ h2n]
    have : (k:ℝ) - i ≤ n := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this hpi.le]
  have hq : 0 ≤ ((k:ℝ) - i) / n := div_nonneg (by linarith) hnpos.le
  have hsinD : ((k:ℝ) - i) / n ≤ sin D := by
    have := Real.mul_le_sin hD0 hDle
    have e : 2 / π * D = ((k:ℝ) - i) / n := by rw [hD]; field_simp; try ring
    linarith
  have hsinS : ((k:ℝ) - i) / n ≤ sin S := by
    have hS0 : 0 ≤ S := div_nonneg (mul_nonneg (by linarith) hpi.le) h2n.le
    by_cases hS2 : S ≤ π / 2
    · have := Real.mul_le_sin hS0 hS2
      have e : 2 / π * S = ((i:ℝ) + k) / n := by rw [hS]; field_simp; try ring
      have : ((k:ℝ) - i) / n ≤ ((i:ℝ) + k) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; linarith
      linarith
    · push Not at hS2
      have hSle : S ≤ π := by
        rw [hS, div_le_iff₀ h2n]
        have : (i:ℝ) + k ≤ 2 * n := by linarith
        nlinarith [mul_le_mul_of_nonneg_right this hpi.le]
      have h0' : 0 ≤ π - S := by linarith
      have h1' : π - S ≤ π / 2 := by linarith
      have := Real.mul_le_sin h0' h1'
      rw [Real.sin_pi_sub] at this
      have e : 2 / π * (π - S) = (2 * (n:ℝ) - i - k) / n := by rw [hS]; field_simp; try ring
      have : ((k:ℝ) - i) / n ≤ (2 * (n:ℝ) - i - k) / n := by
        apply div_le_div_of_nonneg_right _ hnpos.le; linarith
      linarith
  rw [hcos]
  have e : 2 * ((k:ℝ) - i) ^ 2 / (n:ℝ) ^ 2 = 2 * (((k:ℝ) - i) / n) * (((k:ℝ) - i) / n) := by
    field_simp
  rw [e]
  have := mul_le_mul hsinS hsinD hq (hq.trans hsinS)
  nlinarith
end Formalism.SA.P
