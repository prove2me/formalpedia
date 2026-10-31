-- Prove2me | solution 1 for BudgetFeasSubmod.Main.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T19:47:51.723391+00:00
-- url     : https://prove2.me/submissions/58b47565-a426-4221-8af6-ed589d088ee9

import Mathlib
import Definitions.Def_BudgetFeasSubmod_Main_Model
import Theorems.Thm_BudgetFeasSubmod_Main_corollary_3_5
import Theorems.Thm_BudgetFeasSubmod_Main_corollary_3_9

open BudgetFeasSubmod.Main Finset

theorem solution {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (v : Finset A → ℝ) (alg1 : Finset A → (A → ℝ) → Finset A) (alg2 : Finset A → Finset A)
    (tb : Finset A → (Fin 2 → Finset A) → A × Fin 2) (B : ℝ)
    (hv : IsValuation v) (hB : 0 < B)
    (h1 : IsKnapsackEApprox v B alg1) (h1loc : IsCostLocal alg1)
    (h2 : IsUnconstrainedTwoApprox v alg2) (htb : IsArgmaxRule v tb) :
    (∀ ω : Option (Finset A),
      IsTruthful (genSmMain v alg1 alg2 tb B ω) B ∧
        IsIR (genSmMain v alg1 alg2 tb B ω) B ∧
        IsBudgetFeasible (genSmMain v alg1 alg2 tb B ω) B) ∧
    (∀ c : A → ℝ, InDomain B c → opt v c B univ ≤ 505 * expectedValue v alg1 alg2 tb B c) :=
  ⟨corollary_3_5 v alg1 alg2 tb B hv h1loc h2 htb hB,
    fun c hc => corollary_3_9 v alg1 alg2 tb B c hv h1 h2 htb hB hc⟩
