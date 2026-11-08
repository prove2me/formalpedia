-- Prove2me | solution 1 for FoundationsRL.OnlineLearning.eq_1_28
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:34:49.580328+00:00
-- url     : https://prove2.me/submissions/51f0e641-d93c-4f26-829d-1321d2f06415

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_ExponentialWeights
import Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights

open FoundationsRL.OnlineLearning in
theorem solution {X Y : Type*} (F : Finset (X → Y → ℝ)) (hF : ∀ f ∈ F, ∀ x y, 0 ≤ f x y)
    (x : ℕ → X) (y : ℕ → Y) (t : ℕ) (ht : 0 < ∑ f ∈ F, likelihood f x y t) :
    logLoss (ewAveraged F (logDist F x y t) (x t)) (y t) =
      logPotential F x y (t + 1) - logPotential F x y t := by
  have hval : ewAveraged F (logDist F x y t) (x t) (y t)
      = (∑ f ∈ F, likelihood f x y (t + 1)) / (∑ f ∈ F, likelihood f x y t) := by
    unfold ewAveraged logDist
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    unfold likelihood
    rw [Finset.prod_range_succ]
    ring
  have hS1 : 0 ≤ ∑ f ∈ F, likelihood f x y (t + 1) :=
    Finset.sum_nonneg (fun f hf => Finset.prod_nonneg (fun i _ => hF f hf _ _))
  unfold logLoss logPotential negLog
  rw [hval, if_pos ht]
  rcases hS1.lt_or_eq with h | h
  · rw [if_pos (div_pos h ht), if_pos h, ← EReal.coe_sub, Real.log_div h.ne' ht.ne']
    congr 1
    ring
  · rw [← h, zero_div, if_neg (lt_irrefl 0)]
    exact (EReal.top_sub_coe _).symm
