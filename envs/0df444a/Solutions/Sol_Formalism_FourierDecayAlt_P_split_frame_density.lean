-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.split_frame_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:51:28.750262+00:00
-- url     : https://prove2.me/submissions/3e73bfe3-1828-41e4-9c2c-8db7a2fa8d49

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive
import Theorems.Thm_Formalism_FourierDecayAlt_P_s3_split_frame_count
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_densityProduct_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_densityProduct_eq_one_of_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x4_prod_densP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Finset Module Formalism.FourierDecayAlt.P.S3x4 Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.SplitFrameDensity := by
  intro K _ _ n a R
  rw [s3_split_frame_count K n a R]
  have hq : 0 < Fintype.card K := Fintype.card_pos
  set q := Fintype.card K with hqdef
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hρ : R.rank ≤ a := by simpa using R.rank_le_width
  set ρ := R.rank with hρdef
  by_cases h1 : n < a
  · rw [Finset.prod_eq_zero (Finset.mem_range.mpr h1) (by simp),
      densityProduct_eq_zero q _ _ (by omega) (by omega)]
    simp
  rw [not_lt] at h1
  by_cases h2 : n - a < a - ρ
  · rw [Finset.prod_eq_zero (s := range (a - ρ)) (Finset.mem_range.mpr h2) (by simp),
      densityProduct_eq_zero q _ _ (by omega) (by omega)]
    simp
  rw [not_lt] at h2
  have g1 := prod_densP q hq n n le_rfl a h1
  rw [densityProduct_eq_one_of_lt q _ _ (by omega), mul_one] at g1
  have g2 := prod_densP q hq (n - a) n (by omega) (a - ρ) h2
  have e1 : (((n - a : ℕ) : ℤ) + 1) = (n : ℤ) - a + 1 := by omega
  have e2 : (((n - a : ℕ) : ℤ) - ((a - ρ : ℕ) : ℤ) + 1) = (n : ℤ) - a - ((a : ℤ) - ρ) + 1 := by omega
  rw [e1, e2] at g2
  rw [Nat.cast_mul, Nat.cast_mul, g1]
  have : (q : ℝ) ^ (n * a) * densP 1 q ((n : ℤ) - a + 1) n * ((q ^ ((n - a) * ρ) : ℕ) : ℝ) *
      ((∏ j ∈ range (a - ρ), (q ^ (n - a) - q ^ j) : ℕ) : ℝ) =
      (q : ℝ) ^ (n * a) * ((q ^ ((n - a) * ρ) : ℕ) : ℝ) *
      (((∏ j ∈ range (a - ρ), (q ^ (n - a) - q ^ j) : ℕ) : ℝ) * densP 1 q ((n : ℤ) - a + 1) n) := by
    ring
  rw [this, g2, ← mul_assoc]
  congr 1
  push_cast
  rw [← pow_add, ← pow_add, ← zpow_natCast]
  congr 1
  push_cast [Nat.cast_sub h1, Nat.cast_sub hρ]
  ring
end Formalism.FourierDecayAlt.P
