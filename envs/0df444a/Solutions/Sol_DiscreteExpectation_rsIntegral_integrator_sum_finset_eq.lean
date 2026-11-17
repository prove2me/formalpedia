-- Prove2me | solution 1 for DiscreteExpectation.rsIntegral_integrator_sum_finset_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T05:38:52.841323+00:00
-- url     : https://prove2.me/submissions/487e1dde-6d95-4de9-b0a4-30ea2e593b64

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Tactic
import Theorems.Thm_DiscreteExpectation_rsIntegrable_integrator_sum_finset
import Theorems.Thm_DiscreteExpectation_taggedCommonLimit_integrator_sum_finset
import Theorems.Thm_taggedCommonLimit_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open DiscreteExpectation
open scoped BigOperators Pointwise
noncomputable section

theorem solution {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    rsIntegral (fun x => x) (fun x => ∑ i ∈ s, α i x) a b
      (rsIntegrable_integrator_sum_finset s α a b hab h) =
    ∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i) := by
  exact taggedCommonLimit_unique
    (rsIntegral_spec (rsIntegrable_integrator_sum_finset s α a b hab h))
    (taggedCommonLimit_integrator_sum_finset s α a b hab h)
