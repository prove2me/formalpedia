-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.rdOrbInt_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:08.414802+00:00
-- url     : https://prove2.me/submissions/c8cf2e7c-e405-4dff-97eb-d0c6f7ea1830

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Theorems.Thm_Formalism_L2_Pj_FJ_integrableOn_integrand
import Theorems.Thm_Formalism_L2_Pj_FJ_continuous_zAct

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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Pj
open Formalism.L2.Pj.FJ
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
variable {Comp : Type}
variable {K : Type} [Field K] (σ : K →+* ℂ)
variable {C : Type} [AddCommGroup C] [Module K C]
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (hd : OrbDom X ρ) : RdOrbInt σ X ρ rd := by
  intro f cu ph x hx
  exact integrableOn_integrand (hc f cu.1) (continuous_zAct _ _ x) (fun t _ => hd cu t x hx)
end Formalism.L2.Pj.FJ
