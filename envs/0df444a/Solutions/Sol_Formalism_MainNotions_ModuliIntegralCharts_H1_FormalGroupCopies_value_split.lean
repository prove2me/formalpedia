-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.value_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:04.038355+00:00
-- url     : https://prove2.me/submissions/68916b95-7358-4811-98f3-e1672de87e2f

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_dpoly_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_key_left
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_key_right

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
theorem _root_.solution (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (f₁ f₂ ES ET : PS R n d) (hf1 : f₁ ∈ subV R (Vc d S))
    (hf2 : f₂ ∈ subV R (Vc d Sᶜ)) (hES : ES ∈ subV R (Vc d S)) (hET : ET ∈ subV R (Vc d Sᶜ))
    (c1 : constantCoeff ES = 1) (c2 : constantCoeff ET = 1) :
    constantCoeff (DpolyN F cp u (P₁ * P₂) (f₁ * f₂ * (ES * ET))) =
      constantCoeff (DpolyN F cp u P₁ (f₁ * (ES * ET))) *
        constantCoeff (DpolyN F cp u P₂ (f₂ * (ES * ET))) := by
  have hA : f₁ * ES ∈ subV R (Vc d S) := Subalgebra.mul_mem _ hf1 hES
  have hB : f₂ * ET ∈ subV R (Vc d Sᶜ) := Subalgebra.mul_mem _ hf2 hET
  have e1 : f₁ * f₂ * (ES * ET) = (f₁ * ES) * (f₂ * ET) := by ring
  have e2 : f₁ * (ES * ET) = (f₁ * ES) * ET := by ring
  have e3 : f₂ * (ES * ET) = ES * (f₂ * ET) := by ring
  rw [e1, e2, e3, dpoly_mul F cp u S P₁ P₂ h1 h2 _ _ hA hB, key_left F cp u S P₁ h1 _ _ hA hET,
    key_right F cp u S P₂ h2 _ _ hES hB, map_mul, map_mul, map_mul, c1, c2, mul_one, one_mul]
end Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
