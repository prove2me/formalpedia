-- Prove2me | solution 1 for FirstPassageLinearTransport.timeout_word_survives_uniform_barrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:06.345102+00:00
-- url     : https://prove2.me/submissions/b71f4126-a02e-4ec4-af5d-b31d4570a71c

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_timeout_word_survives_exact_barrier
import Theorems.Thm_FirstPassageLinearTransport_wordSurvivesFrom_mono_lower
import Theorems.Thm_FirstPassageLinearTransport_timeout_rank_gap_le_uniform

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ C : ℝ} {L m x : ℕ}
    (hK₀ : 0 ≤ K₀) (hL : 0 < L)
    (hmC : (m : ℝ) ≤ C * (L : ℝ))
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m) :
    wordSurvivesFrom
      (-((C * K₀ / 2 + 3) * Real.log 2))
      collatzLogIncrement m 0 (boolParityWord m x) := by
  have hqle : timeoutTargetRank K₀ L m ≤ m + 2 := hq.trans (by omega)
  have hgapcast :
      (((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ)) =
        (m : ℝ) + 2 - timeoutTargetRank K₀ L m := by
    rw [Nat.cast_sub hqle]
    push_cast
    rfl
  have hgap := timeout_rank_gap_le_uniform hK₀ hL hmC
  apply wordSurvivesFrom_mono_lower
    (lo := -(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2))
  · rw [hgapcast]
    apply neg_le_neg
    gcongr
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · exact timeout_word_survives_exact_barrier hx htimeout hq
end FirstPassageLinearTransport
