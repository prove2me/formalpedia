-- Prove2me | solution 1 for ClassicalComplexWPT.classicalComplexWeierstrassPreparation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:52.19518+00:00
-- url     : https://prove2.me/submissions/2edf1871-5d7a-4210-a535-0ac9f6f92f82

import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Definitions.Def_ClassicalComplexWPT_Main
import Theorems.Thm_ClassicalComplexWPT_exists_isWeierstrassPreparation
import Theorems.Thm_ClassicalComplexWPT_isWeierstrassPreparation_unique


set_option autoImplicit true
open Filter
open scoped BigOperators Topology
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  obtain ⟨a, u, hprep⟩ := exists_isWeierstrassPreparation hf horder
  exact ⟨a, u, hprep, fun _ _ hprep' ↦
    isWeierstrassPreparation_unique hprep hprep'⟩
end ClassicalComplexWPT
