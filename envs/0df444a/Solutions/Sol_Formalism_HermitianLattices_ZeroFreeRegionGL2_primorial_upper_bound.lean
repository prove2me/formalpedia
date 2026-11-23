-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.primorial_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:55.535827+00:00
-- url     : https://prove2.me/submissions/ea3ca8af-2a9f-48c1-a937-9fd8332d2107

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : PrimorialBound := by
  intro y q₁ hy hq
  unfold oddM
  have h1 : (∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p) ≤ primorial ⌊y⌋₊ := by
    unfold primorial
    apply Finset.prod_le_prod_of_subset_of_one_le'
    · intro p hp
      simp only [mem_filter, mem_Icc, mem_range] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p hp _
      exact (mem_filter.1 hp).2.one_lt.le
  have h2 : ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ Real.exp (2 * y) := by
    calc ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ ⌊y⌋₊ : ℕ) : ℝ) := by
          exact_mod_cast h1.trans (primorial_le_four_pow _)
      _ = (4 : ℝ) ^ (⌊y⌋₊ : ℝ) := by push_cast; rw [Real.rpow_natCast]
      _ ≤ (4 : ℝ) ^ y := Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hy)
      _ = Real.exp (Real.log 4 * y) := by rw [Real.rpow_def_of_pos (by norm_num)]
      _ ≤ Real.exp (2 * y) := by
          apply Real.exp_le_exp.2
          have : Real.log 4 ≤ 2 := by
            have : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
            have := Real.log_two_lt_d9
            linarith
          nlinarith
  calc ((q₁ * ∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ)
      = (q₁ : ℝ) * ((∏ p ∈ (Icc 3 ⌊y⌋₊).filter Nat.Prime, p : ℕ) : ℝ) := by push_cast; ring
    _ ≤ Real.exp y * Real.exp (2 * y) := mul_le_mul hq h2 (by positivity) (by positivity)
    _ = Real.exp (3 * y) := by rw [← Real.exp_add]; ring_nf
end Formalism.HermitianLattices.ZeroFreeRegionGL2
