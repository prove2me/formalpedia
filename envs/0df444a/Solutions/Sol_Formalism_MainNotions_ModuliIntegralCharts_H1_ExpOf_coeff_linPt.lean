-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.coeff_linPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:45:26.407078+00:00
-- url     : https://prove2.me/submissions/1c9a87d5-cc69-4797-94d6-5df362d9a1dd

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
theorem _root_.solution (uvec : Lt1 Dw → Fin d → S) (ℓ : Lt1 Dw) (i : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (linPt uvec (0 : Fin 1) i) = uvec ℓ i := by
  classical
  rw [linPt, map_sum]
  simp only [coeff_C_mul, coeff_X]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro ℓ' _ h
    rw [if_neg, mul_zero]
    intro e
    apply h
    have := Finsupp.single_left_injective one_ne_zero e
    exact ((ltIdx Dw).injective (congrArg Prod.snd this)).symm
  · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
