-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.pderiv_cpy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:36:44.299051+00:00
-- url     : https://prove2.me/submissions/426c6f04-6daa-4a76-8400-202ba7e28b3c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_pderiv_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst_cpy

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {S : Type} [CommRing S]
variable {N d : ℕ}
variable (F : Fin d → PS S 2 d) (φ : Fin d → MvPowerSeries (Fin 1 × Fin N) S)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution (b : Fin 2) (q : Fin N) (g : MvPowerSeries (Fin 1 × Fin N) S) :
    pderiv S ((1 : Fin 2), q) (subst (cpy (S := S) b) g) =
      if b = 1 then subst (cpy (S := S) b) (pderiv S ((0 : Fin 1), q) g) else 0 := by
  classical
  rw [pderiv_subst (hasSubst_cpy b), Fintype.sum_prod_type, Fin.sum_univ_one]
  simp only [cpy, pderiv_X, Pi.single_apply, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  by_cases hb : b = 1
  · subst hb
    simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  · simp [hb]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
