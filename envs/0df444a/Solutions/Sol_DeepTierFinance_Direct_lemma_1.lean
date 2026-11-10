-- Prove2me | solution 1 for DeepTierFinance.Direct.lemma_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-11-09T11:14:18.137875+00:00
-- url     : https://prove2.me/submissions/3f01cbd2-f763-4c56-bd74-e3463c01868e

import Definitions.Def_DeepTierFinance_Direct_Primitives

open DeepTierFinance.Direct

noncomputable def primZero : Primitives where
  v := 1 / 2
  P _ := 0

private lemma valid_primZero : primZero.Valid := by
  refine ⟨by norm_num [primZero], by norm_num [primZero], ?_, monotoneOn_const,
    concaveOn_const (0 : ℝ) (convex_Ici 0)⟩
  intro _ _
  exact ⟨le_rfl, zero_lt_one⟩

theorem solution : ¬ (∀ (p : DeepTierFinance.Direct.Primitives) (_hp : p.Valid),
    ∃ c : ℝ, DeepTierFinance.Direct.CapitalOptimum p c ∧
      ∀ θ ∈ Set.Ico 0 c, ∀ r : ℝ, 0 < r →
        ∃ z y : ℝ, DeepTierFinance.Direct.InvestmentFOC p θ r z ∧
          DeepTierFinance.Direct.InvestmentResponse p θ r y ∧
          y = max z θ ∧ DeepTierFinance.Direct.advance θ y = y - θ) := by
  intro h
  rcases h primZero valid_primZero with ⟨c, hcap, _⟩
  have hderiv : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (1 / (1 / 2 : ℝ)) c := hcap.2.2.2
  have hzero : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 c := hasDerivAt_const c (0 : ℝ)
  have heq : (1 / (1 / 2 : ℝ)) = 0 := hderiv.unique hzero
  norm_num at heq
