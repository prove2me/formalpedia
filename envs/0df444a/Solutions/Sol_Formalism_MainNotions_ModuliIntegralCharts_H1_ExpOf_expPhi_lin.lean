-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf.expPhi_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:28.885444+00:00
-- url     : https://prove2.me/submissions/bdb29038-abd9-4d79-8680-c2f65c41e8c1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpOfPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_coeff_single_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_cc_linPt
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpOf_coeff_linPt

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
variable {S : Type} [CommRing S] [Algebra ℚ S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
theorem _root_.solution (uvec : Lt1 Dw → Fin d → S) (ε : Pt S 1 d) (hdε : dLin ε = 1) (ℓ : Lt1 Dw) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), ltIdx Dw ℓ) 1) (expPhi uvec ε j) = uvec ℓ j := by
  classical
  rw [expPhi, coeff_single_subst (fun p : Fin 1 × Fin d => linPt uvec (0 : Fin 1) p.2)
    (fun p => cc_linPt uvec (0 : Fin 1) p.2)]
  simp only [coeff_linPt]
  rw [Fintype.sum_prod_type, Fin.sum_univ_one]
  have hd : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) (ε j) = if j = i then 1 else 0 := fun i => by
    have := congrFun (congrFun hdε j) i
    simpa only [dLin, Matrix.one_apply] using this
  simp only [hd, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpOf
