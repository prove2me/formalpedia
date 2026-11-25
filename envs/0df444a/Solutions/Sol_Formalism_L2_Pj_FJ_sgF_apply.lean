-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.sgF_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:12:04.498199+00:00
-- url     : https://prove2.me/submissions/329031f0-4675-4f94-b10f-9859f23ae551

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Theorems.Thm_Formalism_L2_Pj_FJ_coefVia_apply

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
    (h : RdOrbInt σ X ρ rd) (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) (f : C)
    {x : Frame (X cu.1).Ψ r} (hx : x ∈ (X cu.1).dom) :
    (sgF σ X rd h cu χ f : Frame (X cu.1).Ψ r → ℂ) x =
      coefFn (zAct (X cu.1) cu.2) (phZ (X cu.1) cu.2 χ) (rd f cu.1) x :=
  coefVia_apply _ _ _ _ _ f hx
end Formalism.L2.Pj.FJ
