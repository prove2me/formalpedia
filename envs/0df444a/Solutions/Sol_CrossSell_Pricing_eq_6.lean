-- Prove2me | solution 1 for CrossSell.Pricing.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:28:35.296465+00:00
-- url     : https://prove2.me/submissions/f7062b19-e56b-4675-9c4e-3cf0ca3b54e9

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

open CrossSell.Pricing in
theorem solution {ι κ : Type*} (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) :
    profit S T u c s v p r =
      ∑ i ∈ S.insertNone, mainProb S u p i * (mainMargin c p i + secProfit T s v r i) := by
  unfold profit
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_insertNone]
    simp only [mainMargin, mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    unfold secProfit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
