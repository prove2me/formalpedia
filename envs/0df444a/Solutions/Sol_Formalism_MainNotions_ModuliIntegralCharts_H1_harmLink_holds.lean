-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.harmLink_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:58.167307+00:00
-- url     : https://prove2.me/submissions/12b89c07-a745-4327-9b9f-8b496f3a6511

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndEncPf_colSum_zero

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
open CIndEncPf
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : HarmLinkSt := by
  intro E _ _ _ H Dw l c a n P hP τ hτ i i'
  have key : ∀ b : Fin n,
      MvPolynomial.pderiv (((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
        (MvPolynomial.pderiv (((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b)
          (encP P)) =
      MvPolynomial.rename (ltEquiv Dw n) (MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
        (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P)) := by
    intro b
    unfold encP
    rw [show (((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b) =
        ltEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i', b⟩ from rfl,
      ← MvPolynomial.pderiv_rename (ltEquiv Dw n).injective,
      show (((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ))), b) = ltEquiv Dw n ⟨τ, i, b⟩ from rfl,
      ← MvPolynomial.pderiv_rename (ltEquiv Dw n).injective]
  simp_rw [key]
  rw [← map_sum, colSum_zero c a n P hP τ hτ i i', map_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1
