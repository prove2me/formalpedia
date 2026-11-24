-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.rdOrbInt_of_latZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:09:39.89884+00:00
-- url     : https://prove2.me/submissions/b621bddd-2bbd-4efc-90a9-4791b6c31964

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_Formalism_L2_Pj_FJ_orbDom_of_latZ
import Theorems.Thm_Formalism_L2_Pj_FJ_rdOrbInt_of


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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution {Comp K : Type} [Field K] (σ : K →+* ℂ) {C : Type} [AddCommGroup C]
    [Module K C] (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ))
    (hc : ∀ f c, ContinuousOn (rd f c) (X c).dom) (h : LatZ X ρ) : RdOrbInt σ X ρ rd :=
  rdOrbInt_of σ X rd hc (orbDom_of_latZ X h)
end Formalism.L2.Pj.FJ
