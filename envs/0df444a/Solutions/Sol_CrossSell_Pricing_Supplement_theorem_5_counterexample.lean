-- Prove2me | solution 1 for CrossSell.Pricing.Supplement.theorem_5_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:14.841086+00:00
-- url     : https://prove2.me/submissions/a9c91c13-9add-4afd-a7de-fe7f3c41c3d2

import Mathlib
import Definitions.Def_CrossSell_Pricing_Supplement_Heuristic

open CrossSell
open CrossSell.Pricing
open CrossSell.Pricing.Supplement

/-- The printed hypotheses hold and the actual printed algorithm returns (1,3),
    but the non-prefix secondary set {0,2} has strictly greater true profit. -/
theorem solution :
    PrintedConditions (fun _ : Fin 3 => 0) counterR counterV ∧
    PrintedHeuristic counterU (fun _ : Fin 1 => 0) (fun _ => 1)
      (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 3 ∧
    candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
      (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 3 <
    profit (Finset.univ : Finset (Fin 1)) (fun _ => ({0, 2} : Finset (Fin 3)))
      counterU (fun _ => 0) (fun _ => 0) counterV (fun _ => 1) counterR := by
        have hu : ∀ i : Fin 1, Real.exp (counterU i - 1) = 1/10 := by
          intro i
          have : counterU i - 1 = - Real.log 10 := by unfold counterU; ring
          rw [this, Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
        have hv : ∀ i : Fin 1, ∀ l, Real.exp (counterV (some i) l - counterR l) = 1 := by
          intro i l; simp [counterV]
        have hn : ∀ l : Fin 3, Real.exp (counterV none l - counterR l)
            = if l.val = 2 then 10 else 1/100 := by
          intro l
          have : counterV none l - counterR l = Real.log (if l.val = 2 then 10 else (1 / 100 : ℝ)) := by
            simp only [counterV]; ring
          rw [this, Real.exp_log]
          split_ifs <;> norm_num
        have hgen : ∀ T : Finset (Fin 3),
            profit (Finset.univ : Finset (Fin 1)) (fun _ => T)
              counterU (fun _ => 0) (fun _ => 0) counterV (fun _ => 1) counterR
            = 1/11 + 1/11 * ((∑ l ∈ T, counterR l) / (1 + ∑ l ∈ T, (1:ℝ)))
              + 10/11 * ((∑ l ∈ T, counterR l * (if l.val = 2 then 10 else 1/100))
                  / (1 + ∑ l ∈ T, (if l.val = 2 then (10:ℝ) else 1/100))) := by
          intro T
          unfold profit
          simp only [Finset.sum_insertNone, mainProb, mainDenom, secProb, hu, hv, hn,
            Fin.sum_univ_one, sub_zero]
          set D1 := 1 + ∑ x ∈ T, (if x.val = 2 then (10:ℝ) else 1/100)
          set D2 := 1 + ∑ x ∈ T, (1:ℝ)
          rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
          have e1 : ∀ x ∈ T, counterR x * (1 / (1 + 1 / 10)) *
                  ((if x.val = 2 then (10:ℝ) else 1 / 100) / D1)
                = 10/11 * (counterR x * (if x.val = 2 then (10:ℝ) else 1 / 100) / D1) := by
            intro x _; ring
          have e2 : ∀ x ∈ T, counterR x * (1 / 10 / (1 + 1 / 10)) * (1 / D2)
                = 1/11 * (counterR x / D2) := by
            intro x _; ring
          rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]
          ring
        have hO : offerPrefix (Equiv.refl (Fin 1)) 1 = Finset.univ := by decide
        have hS1 : (secondaryPrefix 1 : Finset (Fin 3)) = {0} := by decide
        have hS2 : (secondaryPrefix 2 : Finset (Fin 3)) = {0, 1} := by decide
        have hS3 : (secondaryPrefix 3 : Finset (Fin 3)) = {0, 1, 2} := by decide
        have hc : ∀ n, candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
            (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 n
            = profit (Finset.univ : Finset (Fin 1)) (fun _ => (secondaryPrefix n : Finset (Fin 3)))
            counterU (fun _ => 0) (fun _ => 0) counterV (fun _ => 1) counterR := by
          intro n; unfold candidateProfit; rw [hO]
        have hP1 : candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
            (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 1
            = 1/11 + 1/11*(10/2) + 10/11*((10/100)/(1+1/100)) := by
          rw [hc, hS1, hgen]; simp [counterR]; norm_num
        have hP2 : candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
            (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 2
            = 1/11 + 1/11*(11/3) + 10/11*((10/100+1/100)/(1+2/100)) := by
          rw [hc, hS2, hgen]; simp [counterR]; norm_num
        have hP3 : candidateProfit counterU (fun _ : Fin 1 => 0) (fun _ => 1)
            (fun _ : Fin 3 => 0) counterR counterV (fun _ => Equiv.refl (Fin 1)) 1 3
            = 1/11 + 1/11*(12/4) + 10/11*((10/100+1/100+10)/(1+2/100+10)) := by
          rw [hc, hS3, hgen]; simp [counterR]; norm_num
        have hP02 : profit (Finset.univ : Finset (Fin 1)) (fun _ => ({0, 2} : Finset (Fin 3)))
            counterU (fun _ => 0) (fun _ => 0) counterV (fun _ => 1) counterR
            = 1/11 + 1/11*(11/3) + 10/11*((1/10+10)/(1+1/100+10)) := by
          rw [hgen]; simp [counterR]; norm_num
        have hR : Antitone counterR := by
          intro a b hab
          revert hab
          fin_cases a <;> fin_cases b <;> simp [counterR]
        refine ⟨?_, ⟨?_, ?_, le_refl _, le_refl _, by norm_num, le_refl _, ?_⟩, ?_⟩
        · intro i
          constructor
          · intro a b hab
            simp only [hv, sub_zero, mul_one]
            exact hR hab
          · intro a b _
            simp only [hv, le_refl]
        · intro a b hab
          simp only [sub_zero]
          exact hR hab
        · intro n' _ _ j k _
          rw [Subsingleton.elim j k]
        · intro m' n' h1 h2 h3 h4
          have hm : m' = 1 := by omega
          subst hm
          interval_cases n'
          · rw [hP1, hP3]; norm_num
          · rw [hP2, hP3]; norm_num
          · exact le_refl _
        · rw [hP3, hP02]; norm_num
