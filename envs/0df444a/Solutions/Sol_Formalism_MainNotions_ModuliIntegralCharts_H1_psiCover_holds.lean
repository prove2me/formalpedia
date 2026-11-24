-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.psiCover_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:00.909966+00:00
-- url     : https://prove2.me/submissions/30a092c7-f1bc-44c9-86a4-8ad90080c102

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_rt0_conj_neg_ne_zero

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (H : Host E) : PsiCoverSt H := by
  intro τ
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have e : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    rw [← map_pow, e]
    simp
  have hpm : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    have h : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
      have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = τ (H.rt : E) ^ 2 - H.rt0 ^ 2 := by ring
      rw [e, hsq, H.sqrt_neg_disc_sq, sub_self]
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h | h
  · exact Or.inl h
  · right
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]
end Formalism.MainNotions.ModuliIntegralCharts.H1
