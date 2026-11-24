-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.isGermFun_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:33:27.698887+00:00
-- url     : https://prove2.me/submissions/79d3ad7e-197e-4863-8374-e3122a5e3590

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_gen_eq_of_corr
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_pull_unique
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_value_unique
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_to__injective_2d1b9ff55e5a
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermFun_psJet_inj

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution : IsGermFunStatement := by
  unfold IsGermFunStatement
  intro E _ _ _ H Dw l Xo c S _ _ y d x act e wP k F f f' h₁ h₂
  have hL : Xo.univ.t.PP.L.IsLB := by
    exact Xo.univ.t.PP.isLB
  apply psJet_inj
  intro m
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := h₁ m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := h₂ m
  have eF := pull_unique (h₁ := hP₁) (h₂ := hP₂)
  subst eF
  have eτ := gen_eq_of_corr (hL := hL) (h₁ := hC₁) (h₂ := hC₂)
  subst eτ
  have ev := value_unique (hL := hL) (h₁ := hV₁) (h₂ := hV₂)
  exact toΓ_injective _ ev
end Formalism.MainNotions.ModuliIntegralCharts.H1
