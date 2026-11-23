-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.pderiv_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:25.921018+00:00
-- url     : https://prove2.me/submissions/7772c459-7052-4afe-ac11-8a99cc58b38f

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
theorem _root_.solution {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [tsub_right_comm]
      congr 1
      simp [Finsupp.single_apply, hij, Ne.symm hij]
      ring
  | add p q hp hq => simp only [map_add, hp, hq]
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
