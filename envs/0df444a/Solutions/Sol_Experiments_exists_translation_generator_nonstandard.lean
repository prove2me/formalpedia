-- Prove2me | solution 1 for Experiments.exists_translation_generator_nonstandard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:45:28.626002+00:00
-- url     : https://prove2.me/submissions/9e1dd1c2-7e12-4da8-a6d1-c9fce59a9d73

import Definitions.Def_Experiments_FiniteDifferenceSemigroup
import Definitions.Def_Experiments_NonstandardSemigroup
import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_Experiments_Translation
import Theorems.Thm_Experiments_exists_eq_exp_of_semigroup_nonstandard
import Theorems.Thm_KernelRank_continuous_shiftCLM
import Theorems.Thm_KernelRank_shiftCLM_add
import Theorems.Thm_KernelRank_shiftCLM_zero


set_option autoImplicit true
open Experiments
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
namespace Experiments
theorem _root_.solution (ψ : ℝ → ℂ)
    [FiniteDimensional ℂ (translateSpan ψ)] (hψ : ContinuousOn ψ (Set.Ici 0)) :
    ∃ a : translateSpan ψ →L[ℂ] translateSpan ψ,
      ∀ t : ℝ, 0 ≤ t → shiftCLM ψ t = NormedSpace.exp ((t : ℂ) • a) := by
  let : NormedAlgebra ℝ (translateSpan ψ →L[ℂ] translateSpan ψ) := .restrictScalars ℝ ℂ _
  obtain ⟨a, ha⟩ := exists_eq_exp_of_semigroup_nonstandard (shiftCLM ψ)
    (continuous_shiftCLM ψ hψ).continuousOn (shiftCLM_zero ψ)
    fun s t hs ht => shiftCLM_add ψ hs ht
  exact ⟨a, ha⟩
end Experiments
