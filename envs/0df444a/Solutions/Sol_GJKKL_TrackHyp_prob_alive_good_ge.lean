-- Prove2me | solution 1 for GJKKL.TrackHyp.prob_alive_good_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:57.691802+00:00
-- url     : https://prove2.me/submissions/a4af2494-be4c-413d-ad3f-33f3cee46a03

module
public import Definitions.Def_GJKKL_Trajectory_Increments
public import Definitions.Def_GJKKL_History_FirstFailure
public import Definitions.Def_GJKKL_Greedy_Counting
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Theorems.Thm_GJKKL_TrackHyp_mass_eq_one
public import Theorems.Thm_GJKKL_TrackHyp_freedman_upperProc
public import Theorems.Thm_GJKKL_TrackHyp_freedman_lowerProc
public import Theorems.Thm_GJKKL_TrackHyp_bad_cases
public import Theorems.Thm_GJKKL_TrackHyp_prob_not_greedy
public import Theorems.Thm_GJKKL_History_prob_alive_ge
public import Theorems.Thm_GJKKL_History_prob_exists_le
public import Theorems.Thm_GJKKL_History_prob_mono
public import Theorems.Thm_GJKKL_History_prob_or_le


set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
open GJKKL.TrackHyp
variable {H : Finset (Finset V)} {k c : ℕ} {dh δ : ℕ → ℝ} {T : ℕ} {B lam C s : ℝ}
  (hyp : TrackHyp H k c dh δ T B lam C s)
include hyp
namespace GJKKL.TrackHyp
theorem _root_.solution :
    1 - T * (2 * Fintype.card V) * Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) ≤
      prob (greedyKernel H) T (AliveBefore (GoodState H dh δ)) := by
  classical
  set ex := Real.exp (-(lam ^ 2 / (2 * C * (lam + s))))
  have hsurv := prob_alive_ge (greedyKernel H) (GoodState H dh δ)
    (fun h hg => hyp.mass_eq_one hg) T
  refine le_trans ?_ hsurv
  have hterm : ∀ i ∈ range T, prob (greedyKernel H) i
      (fun h => AliveBefore (GoodState H dh δ) h ∧ ¬ GoodState H dh δ h) ≤
        2 * Fintype.card V * ex := by
    intro i hi
    have hiT : i < T := mem_range.mp hi
    calc prob (greedyKernel H) i
          (fun h => AliveBefore (GoodState H dh δ) h ∧ ¬ GoodState H dh δ h)
        ≤ prob (greedyKernel H) i (fun h => ¬ IsGreedySeq H h ∨ ∃ v ∈ (univ : Finset V),
            (lam ≤ upperProc H dh δ v h - upperProc H dh δ v [] ∧
              AliveBefore (GoodState H dh δ) h) ∨
            (lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧
              AliveBefore (GoodState H dh δ) h)) :=
          prob_mono _ fun h hh hb => hyp.bad_cases (by omega) hb.1 hb.2
      _ ≤ prob (greedyKernel H) i (fun h => ¬ IsGreedySeq H h) +
            prob (greedyKernel H) i (fun h => ∃ v ∈ (univ : Finset V),
              (lam ≤ upperProc H dh δ v h - upperProc H dh δ v [] ∧
                AliveBefore (GoodState H dh δ) h) ∨
              (lam ≤ lowerProc H dh δ v h - lowerProc H dh δ v [] ∧
                AliveBefore (GoodState H dh δ) h)) := prob_or_le _ _ _ _
      _ ≤ 0 + ∑ v ∈ (univ : Finset V), (ex + ex) := by
          rw [hyp.prob_not_greedy i]
          refine add_le_add le_rfl ((prob_exists_le _ _ _ _).trans (sum_le_sum fun v _ => ?_))
          exact (prob_or_le _ _ _ _).trans (add_le_add (hyp.freedman_upperProc v hiT.le)
            (hyp.freedman_lowerProc v hiT.le))
      _ = 2 * Fintype.card V * ex := by rw [sum_const, card_univ, nsmul_eq_mul]; ring
  have := sum_le_sum hterm
  rw [sum_const, card_range, nsmul_eq_mul] at this
  linarith
end GJKKL.TrackHyp
