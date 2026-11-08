-- Prove2me | solution 1 for FoundationsRL.OnlineLearning.eq_1_29
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:25:43.937134+00:00
-- url     : https://prove2.me/submissions/3985c164-f88a-4069-8241-ec53e662eec3

import Mathlib
import Definitions.Def_FoundationsRL_OnlineLearning_Losses
import Definitions.Def_FoundationsRL_OnlineLearning_LogLossWeights

namespace Aux_FRLeq129

open FoundationsRL.OnlineLearning

theorem negLog_ne_bot (p : ℝ) : negLog p ≠ ⊥ := by
  unfold negLog
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact top_ne_bot

theorem negLog_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : negLog b ≤ negLog a := by
  by_cases ha' : 0 < a
  · have hb : 0 < b := lt_of_lt_of_le ha' hab
    unfold negLog
    rw [if_pos ha', if_pos hb, EReal.coe_le_coe_iff]
    linarith [Real.log_le_log ha' hab]
  · unfold negLog
    rw [if_neg ha']
    exact le_top

theorem negLog_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negLog (a * b) ≤ negLog a + negLog b := by
  by_cases ha' : 0 < a
  · by_cases hb' : 0 < b
    · unfold negLog
      rw [if_pos ha', if_pos hb', if_pos (mul_pos ha' hb'), ← EReal.coe_add,
        Real.log_mul ha'.ne' hb'.ne']
      exact EReal.coe_le_coe_iff.mpr (by linarith)
    · have : negLog b = ⊤ := by unfold negLog; rw [if_neg hb']
      rw [this, EReal.add_top_of_ne_bot (negLog_ne_bot a)]
      exact le_top
  · have : negLog a = ⊤ := by unfold negLog; rw [if_neg ha']
    rw [this, EReal.top_add_of_ne_bot (negLog_ne_bot b)]
    exact le_top

end Aux_FRLeq129

open FoundationsRL.OnlineLearning Aux_FRLeq129 in
theorem solution {X Y : Type*} (F : Finset (X → Y → ℝ)) (hF : ∀ f ∈ F, ∀ x y, 0 ≤ f x y)
    (fstar : X → Y → ℝ) (hfstar : fstar ∈ F) (x : ℕ → X) (y : ℕ → Y) (T : ℕ) :
    logPotential F x y T ≤ ∑ i ∈ Finset.range T, logLoss (fstar (x i)) (y i) := by
  have hlik : ∀ f ∈ F, ∀ t, 0 ≤ likelihood f x y t := by
    intro f hf t
    exact Finset.prod_nonneg (fun i _ => hF f hf _ _)
  have hind : ∀ t, negLog (likelihood fstar x y t) ≤
      ∑ i ∈ Finset.range t, logLoss (fstar (x i)) (y i) := by
    intro t
    induction t with
    | zero =>
      simp [likelihood, negLog]
    | succ t ih =>
      have e : likelihood fstar x y (t + 1) = likelihood fstar x y t * fstar (x t) (y t) := by
        unfold likelihood
        rw [Finset.prod_range_succ]
      rw [e, Finset.sum_range_succ]
      calc negLog (likelihood fstar x y t * fstar (x t) (y t))
          ≤ negLog (likelihood fstar x y t) + negLog (fstar (x t) (y t)) :=
            negLog_mul (hlik fstar hfstar t) (hF fstar hfstar _ _)
        _ ≤ ∑ i ∈ Finset.range t, logLoss (fstar (x i)) (y i) + logLoss (fstar (x t)) (y t) :=
            add_le_add ih le_rfl
  have hle : likelihood fstar x y T ≤ ∑ f ∈ F, likelihood f x y T :=
    Finset.single_le_sum (f := fun f => likelihood f x y T) (fun f hf => hlik f hf T) hfstar
  exact le_trans (negLog_anti (hlik fstar hfstar T) hle) (hind T)
