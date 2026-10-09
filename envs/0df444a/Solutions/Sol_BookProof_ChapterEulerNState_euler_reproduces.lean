-- Prove2me | solution 1 for BookProof.ChapterEulerNState.euler_reproduces
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:52:13.609457+00:00
-- url     : https://prove2.me/submissions/865ec5a5-ba26-46e5-87ae-359086c912cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.euler_reproduces
import Mathlib
import Definitions.Def_ChapterEulerNState
import Theorems.Thm_BookProof_ChapterEulerNState_tailProd_succ
import Theorems.Thm_BookProof_ChapterEulerNState_tailSum_succ
import Theorems.Thm_BookProof_ChapterEulerNState_tailSum_last
import Theorems.Thm_BookProof_ChapterEulerNState_exists_theta_tailProd
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {n : ℕ} (hn : 1 ≤ n)
    (hsum : ∑ j ∈ Finset.range n, p j = 1) :
    ∃ θ : ℕ → ℝ, ∀ k < n, bornProb θ n k = p k := by

  obtain ⟨ θ, hθ ⟩ := exists_theta_tailProd p hp hsum;
  refine ⟨θ, fun k hk => ?_⟩
  by_cases h : k + 1 < n;
  · convert congr_arg₂ ( · - · ) ( hθ k ( by linarith ) ) ( hθ ( k + 1 ) ( by linarith ) ) using 1;
    · unfold bornProb; simp only [h, if_true, tailProd_succ, Real.sin_sq]; ring
    · rw [ tailSum_succ _ _ _ h.le, add_sub_cancel_right ];
  · have hk1 : k + 1 = n := by omega
    have hkn : k ≤ n := by omega
    unfold bornProb
    rw [if_neg h, if_pos hk1, hθ k hkn]
    have : k = n - 1 := by omega
    rw [this, tailSum_last p hn]
