-- Prove2me | solution 1 for Deduction.Gchi_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:18:41.911106+00:00
-- url     : https://prove2.me/submissions/1885421f-0f62-486d-aaaf-65e415d19a07

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_LFunctionConj
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_GchiConj
import Theorems.Thm_Deduction_Gchi_conj_ramp
import Theorems.Thm_Deduction_Gchi_conj_LFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace Deduction
private theorem deriv_conj_comp_conj (f : ℂ → ℂ) (x : ℂ) :
    deriv ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) =
      (starRingEnd ℂ) (deriv f x) := by
  by_cases hf : DifferentiableAt ℂ f x
  · exact hf.hasDerivAt.conj_conj.deriv
  · have hg : ¬ DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) ((starRingEnd ℂ) x) := by
      rw [differentiableAt_conj_conj_iff, Complex.conj_conj]
      exact hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hg, map_zero]
end Deduction
end
end

set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (starRingEnd ℂ) (Gchi χ y) = Gchi χ⁻¹ y := by
  by_cases h1 : χ = 1
  · subst h1
    simp only [Gchi, inv_one, if_true]
    rw [map_add, map_sub, Gchi_conj_ramp, inv_one, Complex.conj_ofReal, Complex.conj_ofReal]
  · have h2 : χ⁻¹ ≠ 1 := fun h => h1 (inv_eq_one.mp h)
    simp only [Gchi, h1, h2, if_false]
    have hL := Gchi_conj_LFunction χ
    have h1c : (starRingEnd ℂ) (1 : ℂ) = 1 := map_one _
    rw [map_add, map_mul, map_div₀, Gchi_conj_ramp, Complex.conj_ofReal, hL]
    congr 2
    rw [← h1c, deriv_conj_comp_conj, h1c]
    simp only [Function.comp_apply, h1c]
end Deduction
