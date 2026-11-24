-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA.psJet_prod_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:48:01.053191+00:00
-- url     : https://prove2.me/submissions/a1790eea-6ea7-4b33-a8c3-9d4f26955481

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
theorem _root_.solution {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (D : ℕ)
    {f g : κ → MvPowerSeries ι R} (h : ∀ b, psJet D (f b) = psJet D (g b)) :
    psJet D (∏ b, f b) = psJet D (∏ b, g b) := by
  change psJetM D (∏ b, f b) = psJetM D (∏ b, g b)
  rw [map_prod, map_prod]
  exact Finset.prod_congr rfl fun b _ => h b
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvA
