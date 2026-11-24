-- Prove2me | solution 1 for Formalism.ZF.zetaPrimeSum_nonneg_and_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:43:11.886352+00:00
-- url     : https://prove2.me/submissions/f0f0b5f3-d41e-4e2c-b5c4-b60f3c1f3666

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfOneLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
open ArithmeticFunction
namespace Formalism.ZF
theorem _root_.solution (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, 0 ≤ ArithmeticFunction.vonMangoldt n * (y / n - 1) ∧
      ArithmeticFunction.vonMangoldt n * (y / n - 1) ≤ Real.log y * y := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hy0)
    have h1 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos]
      linarith
    have h2 : y / n - 1 ≤ y := by
      have : y / n ≤ y := div_le_self hy0 hn1'
      linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hny)
    exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1, mul_le_mul hΛ h2 h1 hlog⟩
  unfold Formalism.Sz
  refine ⟨Finset.sum_nonneg fun n hn => (hterm n hn).1, ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log y * y := Finset.sum_le_sum fun n hn => (hterm n hn).2
    _ = (⌊y⌋₊ : ℝ) * (Real.log y * y) := by simp
    _ ≤ y * (Real.log y * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy0) (mul_nonneg hlog hy0)
    _ = y * y * Real.log y := by ring
end Formalism.ZF
