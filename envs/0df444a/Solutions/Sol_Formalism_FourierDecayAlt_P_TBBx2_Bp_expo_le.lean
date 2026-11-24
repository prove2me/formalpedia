-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Bp.expo_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:26.124938+00:00
-- url     : https://prove2.me/submissions/d1e30a12-2619-4384-968e-7ae86cb37a7f

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Bp
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB MeasureTheory
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P.TBBx2.Bp
theorem _root_.solution (C₃ CΛ C₀ L K : ℝ) (r n₀ p₀ : ℕ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hn₀ : n₀ ≤ 30 * (r + 1) ^ 2 + 6) (hp₀ : (p₀ : ℝ) ≤ C₀ * (3 * ((r : ℝ) + 1)) + 1) :
    1 + ((4 * n₀ : ℕ) : ℝ) + K * ((2 * r + 2 : ℕ) : ℝ) ^ 2 +
        (L + 2 * (CΛ * ((2 * r + 2 : ℕ) : ℝ))) * ((r + 1 : ℕ) : ℝ) +
        2 * C₃ * ((2 * r + 2 : ℕ) : ℝ) ^ 2 * ((2 * p₀ + n₀ : ℕ) : ℝ) ≤
      (40 + CΛ + L + K + 2 * C₃ * (3 * C₀ + 10)) * ((2 * r + 2 : ℕ) : ℝ) ^ 4 := by
  push_cast
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hs : 1 ≤ s := by rw [hs_def]; linarith
  have hn : (n₀ : ℝ) ≤ 30 * s ^ 2 + 6 := by
    rw [hs_def]; exact_mod_cast hn₀
  have hp : (p₀ : ℝ) ≤ C₀ * (3 * s) + 1 := by rw [hs_def]; exact hp₀
  have hr : (r : ℝ) = s - 1 := by rw [hs_def]; ring
  rw [hr]
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hs12 : s ≤ s ^ 2 := by nlinarith
  have hs24 : s ^ 2 ≤ s ^ 4 := by nlinarith
  have hs14 : s ≤ s ^ 4 := hs12.trans hs24
  have hs4 : 0 ≤ s ^ 4 := by positivity
  have hA : 1 + 4 * (n₀ : ℝ) ≤ 40 * (2 * s) ^ 4 := by nlinarith
  have hB : K * (2 * s) ^ 2 ≤ K * (2 * s) ^ 4 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hK
  have hC1 : L * s ≤ L * s ^ 4 := mul_le_mul_of_nonneg_left hs14 hL
  have hC2 : CΛ * s ^ 2 ≤ CΛ * s ^ 4 := mul_le_mul_of_nonneg_left hs24 hCΛ
  have hC3 : 0 ≤ L * s ^ 4 := mul_nonneg hL hs4
  have hC4 : 0 ≤ CΛ * s ^ 4 := mul_nonneg hCΛ hs4
  have hC0 : 0 ≤ C₀ := by linarith
  have hq1 : C₀ * s ≤ C₀ * s ^ 2 := mul_le_mul_of_nonneg_left hs12 hC0
  have hq2 : 0 ≤ C₀ * s ^ 2 := mul_nonneg hC0 (by positivity)
  have hq : 2 * (p₀ : ℝ) + n₀ ≤ (3 * C₀ + 10) * (4 * s ^ 2) := by nlinarith
  have hD : 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀) ≤ 2 * C₃ * (3 * C₀ + 10) * (2 * s) ^ 4 := by
    calc 2 * C₃ * (2 * s) ^ 2 * (2 * (p₀ : ℝ) + n₀)
        ≤ 2 * C₃ * (2 * s) ^ 2 * ((3 * C₀ + 10) * (4 * s ^ 2)) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg (by norm_num) hC₃) (sq_nonneg _))
      _ = 2 * C₃ * (3 * C₀ + 10) * (2 * s) ^ 4 := by ring
  linarith [hA, hB, hC1, hC2, hC3, hC4, hD]
end Formalism.FourierDecayAlt.P.TBBx2.Bp
