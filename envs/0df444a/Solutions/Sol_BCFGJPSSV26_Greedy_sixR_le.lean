-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.sixR_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:55.166125+00:00
-- url     : https://prove2.me/submissions/ca394d8e-d2c2-4d8f-a36b-0ed54d630dd4

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants
import all Definitions.Def_BCFGJPSSV26_Greedy_Constants

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- **The free atoms of the core**: when `n > ⌊log₂ n⌋ ⌈1/δ²⌉` and `n ≥ 2`,
`6 R ≤ C log n / ε²`. -/
theorem sixR_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) {n : ℕ} (hbn : bcomp (constsOf ε) n < n)
    (hn : 2 ≤ n) : ((6 * Rof (constsOf ε) n : ℕ) : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by
  obtain ⟨hδ0, hδ1, hg, hp⟩ := constsOf_rel hε
  have h := sixR_le_aux hδ0 hδ1 hg hp hbn hn
  have h' : ((6 * Rof (constsOf ε) n : ℕ) : ℝ) ≤
      7278 * Nat.log 2 n * (1 / ((constsOf ε).δ : ℝ) ^ 2) := by
    exact_mod_cast h
  have hq := inv_δ_sq_le hε h4
  have hL := natLog_two_le_two_log n
  have hlog := Real.log_natCast_nonneg n
  have hu : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  have he : Cthm * Real.log n / ε ^ 2 = 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by
    unfold Cthm
    ring
  have he' : (160000 : ℝ) / ε ^ 2 = 160000 * (1 / ε ^ 2) := by ring
  rw [he]
  rw [he'] at hq
  have hδ0' : (0 : ℝ) < (constsOf ε).δ := by exact_mod_cast hδ0
  calc ((6 * Rof (constsOf ε) n : ℕ) : ℝ)
      ≤ 7278 * Nat.log 2 n * (1 / ((constsOf ε).δ : ℝ) ^ 2) := h'
    _ ≤ 7278 * (2 * Real.log n) * (160000 * (1 / ε ^ 2)) := by
        have := Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)
        gcongr
    _ ≤ 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by nlinarith

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.sixR_le := @BCFGJPSSV26.Greedy.sixR_le
