-- Prove2me | solution 1 for FinancialDerivatives.FD03.snell_eq_max_policy_value
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:11:40.55587+00:00
-- url     : https://prove2.me/submissions/8299c38f-a873-4002-8216-16c0ba4053fb

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_snellValue
import Definitions.Def_fd03_policyValue
import Definitions.Def_fd03_admissible
open FinancialDerivatives.FD03
theorem solution (m : BinomialMarket) (n : ℕ)
    (exercise : ExerciseTree n) :
    ∃ p : StoppingPolicy n,
      admissible exercise p ∧
      policyValue m n exercise p = snellValue m n exercise ∧
      ∀ other : StoppingPolicy n,
        admissible exercise other →
          policyValue m n exercise other ≤ policyValue m n exercise p := by
  have mono : ∀ u₁ u₂ d₁ d₂ : ℝ, u₁ ≤ u₂ → d₁ ≤ d₂ → oneStepValue m u₁ d₁ ≤ oneStepValue m u₂ d₂ := by
    intro u₁ u₂ d₁ d₂ hu hd
    unfold oneStepValue
    have h0 : 0 < upWeight m := by
      unfold upWeight
      exact div_pos (by linarith [m.down_lt_growth]) (by linarith [m.down_lt_growth, m.growth_lt_up])
    have h1 : upWeight m < 1 := by
      unfold upWeight
      rw [div_lt_one (by linarith [m.down_lt_growth, m.growth_lt_up])]
      linarith [m.growth_lt_up]
    have hg : 0 < m.growth := by linarith [m.down_pos, m.down_lt_growth]
    apply div_le_div_of_nonneg_right _ hg.le
    nlinarith
  have le : ∀ (n : ℕ) (tree : ExerciseTree n) (p : StoppingPolicy n), admissible tree p →
      policyValue m n tree p ≤ snellValue m n tree := by
    intro n tree p hp
    induction tree with
    | maturity r => cases p; rfl
    | node a r u d ihu ihd =>
      cases p with
      | stop =>
        simp only [admissible] at hp
        subst hp
        exact le_max_left _ _
      | «continue» pu pd =>
        obtain ⟨h1, h2⟩ := hp
        have hc : policyValue m _ (.node a r u d) (.continue pu pd) ≤
            oneStepValue m (snellValue m _ u) (snellValue m _ d) := mono _ _ _ _ (ihu pu h1) (ihd pd h2)
        cases a
        · exact hc
        · exact hc.trans (le_max_right _ _)
  have ex : ∀ (n : ℕ) (tree : ExerciseTree n), ∃ p : StoppingPolicy n,
      admissible tree p ∧ policyValue m n tree p = snellValue m n tree := by
    intro n tree
    induction tree with
    | maturity r => exact ⟨.maturity, trivial, rfl⟩
    | node a r u d ihu ihd =>
      obtain ⟨pu, hu1, hu2⟩ := ihu
      obtain ⟨pd, hd1, hd2⟩ := ihd
      cases a
      · refine ⟨.continue pu pd, ⟨hu1, hd1⟩, ?_⟩
        show oneStepValue m _ _ = oneStepValue m _ _
        rw [hu2, hd2]
      · by_cases h : oneStepValue m (snellValue m _ u) (snellValue m _ d) ≤ r
        · refine ⟨.stop, rfl, ?_⟩
          show r = max r _
          exact (max_eq_left h).symm
        · refine ⟨.continue pu pd, ⟨hu1, hd1⟩, ?_⟩
          show oneStepValue m _ _ = max r (oneStepValue m _ _)
          rw [hu2, hd2, max_eq_right (le_of_lt (not_le.mp h))]
  obtain ⟨p, hp1, hp2⟩ := ex n exercise
  exact ⟨p, hp1, hp2, fun o ho => hp2 ▸ le n exercise o ho⟩


