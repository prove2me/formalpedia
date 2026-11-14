-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.bcomp_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:54.272425+00:00
-- url     : https://prove2.me/submissions/85076fa2-60fb-40ab-9720-dfd31c1aa22a

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants
import all Definitions.Def_BCFGJPSSV26_Greedy_Constants

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- **The extra facilities of the trivial solution**: `⌊log₂ n⌋ ⌈1/δ²⌉ ≤ C log n / ε²`. -/
theorem bcomp_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) (n : ℕ) :
    (bcomp (constsOf ε) n : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by
  have hq := inv_δ_sq_le hε h4
  obtain ⟨hδ0, hδ1, -, -⟩ := constsOf_rel hε
  have hL := natLog_two_le_two_log n
  have hlog := Real.log_natCast_nonneg n
  have hδ0' : (0 : ℝ) < (constsOf ε).δ := by exact_mod_cast hδ0
  have hδ1' : ((constsOf ε).δ : ℝ) ≤ 1 / 100 := by
    have h := (Rat.cast_le (K := ℝ)).2 hδ1
    rwa [show ((1 / 100 : ℚ) : ℝ) = 1 / 100 by norm_num] at h
  -- `⌈1/δ²⌉ ≤ 1/δ² + 1 ≤ 2/δ²`
  have hA : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) ≤ 2 * (1 / ((constsOf ε).δ : ℝ) ^ 2) := by
    have h1 : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℚ) < 1 / (constsOf ε).δ ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) < 1 / ((constsOf ε).δ : ℝ) ^ 2 + 1 := by
      exact_mod_cast h1
    have h3 : (1 : ℝ) ≤ 1 / ((constsOf ε).δ : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hu : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  have he : Cthm * Real.log n / ε ^ 2 = 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by
    unfold Cthm
    ring
  have he' : (160000 : ℝ) / ε ^ 2 = 160000 * (1 / ε ^ 2) := by ring
  rw [he]
  rw [he'] at hq
  unfold bcomp
  push_cast
  have hA' : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) ≤ 320000 * (1 / ε ^ 2) := by linarith
  calc (Nat.log 2 n : ℝ) * (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ)
      ≤ (2 * Real.log n) * (320000 * (1 / ε ^ 2)) :=
        mul_le_mul hL hA' (Nat.cast_nonneg _) (by positivity)
    _ ≤ 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by nlinarith

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.bcomp_le := @BCFGJPSSV26.Greedy.bcomp_le
