-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.subst_linPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:25.5716+00:00
-- url     : https://prove2.me/submissions/5cd70fc0-4ba1-4ca5-a200-4e81c5275fed

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
variable {S : Type} [CommRing S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution {n m : ℕ} (uvec : Lt1 Dw → Fin d → S) (b : Fin n)
    (a : Fin n × Fin (dL Dw) → MvPowerSeries (Fin m × Fin (dL Dw)) S) (ha : HasSubst a) (i : Fin d) :
    subst a (linPt uvec b i) = ∑ ℓ : Lt1 Dw, MvPowerSeries.C (uvec ℓ i) * a (b, ltIdx Dw ℓ) := by
  rw [linPt, ← coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [map_mul, coe_substAlgHom, subst_X ha]
  congr 1
  rw [MvPowerSeries.subst_C]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
