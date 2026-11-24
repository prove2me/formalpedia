-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_iterate_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:47:57.714499+00:00
-- url     : https://prove2.me/submissions/e788acab-a35e-4da1-b4f1-11ae453fa0c1

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
theorem _root_.solution {σ R : Type} [CommRing R] (i : σ) (k : ℕ) :
    ∀ (F : MvPowerSeries σ R) (N : σ →₀ ℕ), coeff N ((pderiv R i)^[k] F) =
      (∏ t ∈ Finset.range k, ((N i + t + 1 : ℕ) : R)) * coeff (N + k • Finsupp.single i 1) F := by
  induction k with
  | zero => intro F N; simp
  | succ k ih =>
    intro F N
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv, Finset.prod_range_succ]
    have e1 : (N + k • Finsupp.single i 1 : σ →₀ ℕ) i = N i + k := by simp
    have e2 : N + k • Finsupp.single i 1 + Finsupp.single i 1 = N + (k + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [e1, e2]
    push_cast
    ring
end Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
