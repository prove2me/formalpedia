-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.coin_cost_measurable
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:31:19.084507+00:00
-- url     : https://prove2.me/submissions/03d4364c-0189-4384-be83-2342090d3f14

import Definitions.Def_CountingLLL_CoinCost
import Theorems.Thm_CountingLLL_ReciprocalTest_coin_cost_geometric_all
set_option autoImplicit false
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem solution : Measurable coinOracleCost := by
  classical
  let T : (ℕ → Bool × Bool) → ℝ≥0∞ := fun x => ∑' k : ℕ,
    ({y : ℕ → Bool × Bool | ∀ i < k, y i = (false,false)}).indicator (1 : (ℕ → Bool × Bool) → ℝ≥0∞) x
  have hT : Measurable T := by
    apply Measurable.tsum
    intro k
    apply Measurable.indicator measurable_const
    have heq : {y : ℕ → Bool × Bool | ∀ i < k, y i = (false,false)} =
        ⋂ i : Fin k, {y | y i.val = (false,false)} := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h i; exact h i.val i.isLt
      · intro h i hi; exact h ⟨i,hi⟩
    rw [heq]
    exact MeasurableSet.iInter fun i => (MeasurableSet.singleton _).preimage (measurable_pi_apply i.val)
  let pair : Entropy → (ℕ → Bool × Bool) := fun ω n => (ω.1 n, ω.2.1 n)
  have hpair : Measurable pair := by fun_prop
  have heq : coinOracleCost = T ∘ pair := by
    funext ω
    exact coin_cost_geometric_all ω
  rw [heq]
  exact hT.comp hpair
