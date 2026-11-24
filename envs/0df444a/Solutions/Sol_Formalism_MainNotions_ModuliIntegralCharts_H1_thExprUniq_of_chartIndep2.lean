-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.thExprUniq_of_chartIndep2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:34.323663+00:00
-- url     : https://prove2.me/submissions/36f0f718-70fc-403e-ba77-c48b4131903b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndSt
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2

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
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution (hC : ChartIndepSt2) : ThExprUniqSt := by
  intro E _ _ _ H Dw l Xo c _ nab₁ nab₂ h₁ h₂ S _ _ _ y k n F a P hP
  obtain ⟨C₁, hex₁, hpin₁⟩ := h₁.2 S y
  obtain ⟨C₂, hex₂, hpin₂⟩ := h₂.2 S y
  choose f₁ hf₁ using fun b => hex₁ k (F b)
  choose f₂ hf₂ using fun b => hex₂ k (F b)
  have e₁ : ∀ m, ∏ b, nab₁ y k (F b) (colOf m b) =
      ∏ b, C₁.B.nabVal S C₁.h H.w0 k (f₁ b) C₁.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₁ k (F b) (f₁ b) (hf₁ b) (colOf m b)
  have e₂ : ∀ m, ∏ b, nab₂ y k (F b) (colOf m b) =
      ∏ b, C₂.B.nabVal S C₂.h H.w0 k (f₂ b) C₂.uvec (MvPolynomial.monomial (colOf m b) 1) := fun m =>
    Finset.prod_congr rfl fun b _ => hpin₂ k (F b) (f₂ b) (hf₂ b) (colOf m b)
  have h := hC E H Dw l Xo c h₁.1 S y C₁ C₂ k n F f₁ f₂ hf₁ hf₂ a P hP
  simp only [chartVal] at h
  simp only [e₁, e₂]
  exact h
end Formalism.MainNotions.ModuliIntegralCharts.H1
