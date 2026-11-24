-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:31:17.135052+00:00
-- url     : https://prove2.me/submissions/a6e10369-05e3-447e-a20a-bcf4e343976c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PhiCMinA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_cj
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_integral
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_smul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PhiCMin_cj_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]
variable {cj : E → E} (hcj : ∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z))
include hcj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
theorem _root_.solution (hne : ∃ z : E, cj z ≠ z) :
    ∃ θ : 𝓞 E, (θ : E) ≠ 0 ∧ cj (θ : E) = -(θ : E) := by
  obtain ⟨z, hz⟩ := hne
  have hex : ∃ c : 𝓞 E, cj (c : E) ≠ c := by
    by_contra hall
    push_neg at hall
    apply hz
    let f : E →ₗ[ℚ] E :=
      { toFun := cj, map_add' := cj_add hcj, map_smul' := fun q a => cj_smul hcj q a }
    have hf : f = LinearMap.id := (integralBasis E).ext fun i => by
      show cj (integralBasis E i) = integralBasis E i
      rw [integralBasis_apply]
      exact hall _
    exact LinearMap.congr_fun hf z
  obtain ⟨c, hc⟩ := hex
  obtain ⟨c', hc'⟩ := cj_integral hcj c
  have hθ : ((c - c' : 𝓞 E) : E) = (c : E) - cj (c : E) := by
    rw [← hc']
    first | rfl | (push_cast; rfl) | norm_cast
  refine ⟨c - c', ?_, ?_⟩
  · rw [hθ]
    exact sub_ne_zero.mpr (Ne.symm hc)
  · rw [hθ, sub_eq_add_neg, cj_add hcj, cj_neg hcj, cj_cj hcj]
    ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
