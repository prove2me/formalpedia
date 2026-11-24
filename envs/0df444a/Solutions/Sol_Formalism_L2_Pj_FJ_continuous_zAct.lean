-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.continuous_zAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:15:57.46317+00:00
-- url     : https://prove2.me/submissions/f9c8df97-8ce4-471d-ba21-2950c9227d07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand

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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (x : Frame X.Ψ r) :
    Continuous fun t => zAct X cu t x := by
  unfold zAct zMatC
  fun_prop
end Formalism.L2.Pj.FJ
