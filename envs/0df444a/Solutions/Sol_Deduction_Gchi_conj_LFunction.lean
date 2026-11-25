-- Prove2me | solution 1 for Deduction.Gchi_conj_LFunction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:31.880462+00:00
-- url     : https://prove2.me/submissions/45830779-d0af-4a53-b43d-a5092d89aa38

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Theorems.Thm_Deduction_LFunction_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.LFunction χ⁻¹ =
      (starRingEnd ℂ) ∘ DirichletCharacter.LFunction χ ∘ (starRingEnd ℂ) := by
  funext s
  have h := LFunction_conj χ ((starRingEnd ℂ) s)
  rw [Complex.conj_conj] at h
  simp only [Function.comp_apply]
  exact h
end Deduction
