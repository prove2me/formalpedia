-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC.colIdx_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:55.71763+00:00
-- url     : https://prove2.me/submissions/ee79908b-bbcf-4ceb-b4c6-b9740932b0ce

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvA
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_KillAddFin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_HarmInvC

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (m : LtN Dw n →₀ ℕ) : (colIdx m).degree = m.degree := by
  classical
  have key : ∀ {α : Type} (e : α →₀ ℕ), e.degree = e.sum (fun _ k => k) := fun e => rfl
  rw [colIdx, key, key, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
end Formalism.MainNotions.ModuliIntegralCharts.H1.HarmInvC
