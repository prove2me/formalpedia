-- Prove2me | solution 1 for Formalism.CountingSumsFrames.interval_kappa_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:52.871791+00:00
-- url     : https://prove2.me/submissions/e4f82bfd-5bc2-44c6-a1b6-fa08543e3587

import Mathlib
import Definitions.Def_Formalism_PolynomialDimension_ApolarComparisonExponent
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_ParamsI
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_IntervalCleanDepthBound
import Theorems.Thm_Formalism_CountingSumsFrames_IntervalBounds_basics
import Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_cnkc
import Theorems.Thm_Formalism_CountingSumsFrames_ParamsIProof_share


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
open ParamsIProof IntervalBounds
namespace Formalism.CountingSumsFrames
theorem _root_.solution : KapI := by
  intro CW C1 hCW hC1
  refine ⟨3 * C1 + 1000 * CW + 1002, by linarith, ?_⟩
  intro C₀ hC₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar h mH mHp hmH hmHp
  obtain ⟨hN, hN1, hk5, hJ1, hJN, hp25, hQ, ha0, hL1, hl1, hlg0, hlg, hLa1, hNk, sq_level_le_degree, hD0, hb1⟩ :=
    basics _ C₀ p N N₁ J k n' G' Y Yb a b' Ib cl D cStar (by linarith) hC₀ h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19,
    g20, g21, g22, g23, g24⟩ := h
  generalize hCdef : 3 * C1 + 1000 * CW + 1002 = C at *
  have hC0 : 0 < C := by linarith
  have hY0 : 0 < Y := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hNcl : 0 ≤ (N : ℝ) * cl := by positivity
  have hncl : 0 ≤ (n' : ℝ) * cl := by positivity
  have hQ4 : 1 ≤ ((p : ℝ) ^ G') ^ 4 := one_le_pow₀ hQ
  have hM : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ b' := by
    have e1 : C * (k : ℝ) ^ 3 * Y * (N * cl) ≤ C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) ≤
        C * (k : ℝ) ^ 3 * Y * (cStar + N * cl + n' * cl) * (N * ((p : ℝ) ^ G') ^ 4) :=
      le_mul_of_one_le_right (mul_nonneg (by positivity) (by linarith))
        (one_le_mul_of_one_le_of_one_le hN hQ4)
    linarith
  have hsh := share C k Y (N * cl) a b' Ib Yb N (logScale C₀ N₁ a) (Real.log a) (by linarith)
    (by linarith) g2 hNcl hM g17 (by linarith) hN hLa1 hL1 g16 g12
  have hcn := cnkc C (CW + 1) k Y N cl b' (by linarith) (by linarith) (by linarith) g2
    (by linarith) g20 g17 hM
  have hcn2 : CW * N * k * (2 * cl) / b' ≤ (CW + 1) * N * k * (2 * cl) / b' := by
    apply div_le_div_of_nonneg_right _ g17.le
    have : 0 ≤ (N : ℝ) * k * (2 * cl) := by positivity
    linarith
  have hinv : 1 / (a / ((k : ℝ) * Y)) = k * Y / a := one_div_div _ _
  rw [hinv]
  have hNN : 1 ≤ (N : ℝ) * N₁ := one_le_mul_of_one_le_of_one_le hN hN1
  have hY1 : 1 / Y ≤ (N : ℝ) * N₁ / Y := div_le_div_of_nonneg_right hNN hY0.le
  have hZ : 0 ≤ (N : ℝ) * N₁ / Y := by positivity
  have e1 : C1 * N * N₁ / Y = C1 * ((N : ℝ) * N₁ / Y) := by ring
  have e2 : C * N * N₁ / Y = C * ((N : ℝ) * N₁ / Y) := by ring
  have e3 : (3 * C1 + 2) * ((N : ℝ) * N₁ / Y) ≤ C * ((N : ℝ) * N₁ / Y) :=
    mul_le_mul_of_nonneg_right (by linarith) hZ
  rw [e1] at hmH hmHp
  rw [e2]
  linarith
end Formalism.CountingSumsFrames
