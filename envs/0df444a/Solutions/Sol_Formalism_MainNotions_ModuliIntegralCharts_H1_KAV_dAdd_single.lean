-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.dAdd_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:59.585999+00:00
-- url     : https://prove2.me/submissions/068732f1-9fa1-4af6-a86a-45497a500543

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd

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
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
theorem _root_.solution {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) (G : Germ.PS S n d) :
    TB.dAdd (Pi.single j 1) b G = pderiv S (b, j) G := by
  unfold TB.dAdd
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [Pi.single_apply, hj']
  · intro h
    exact absurd (Finset.mem_univ j) h
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
