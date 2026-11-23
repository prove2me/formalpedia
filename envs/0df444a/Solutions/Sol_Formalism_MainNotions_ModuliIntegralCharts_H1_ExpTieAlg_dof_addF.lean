-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg.dof_addF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:39.616794+00:00
-- url     : https://prove2.me/submissions/d317cfca-33b0-431d-a855-72825a175030

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpTieAlg_hasSubst0

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
theorem _root_.solution (u : Fin N → S) (g : PS S 1 N) :
    Dof (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N) u g = ∑ j, C (u j) * pderiv S ((0 : Fin 1), j) g := by
  classical
  have hs : HasSubst (fun p : Fin 2 × Fin N => (![pt S N 0, 0] : Fin 2 → Pt S 1 N) p.1 p.2) :=
    hasSubst0 (by rintro ⟨b, i⟩; fin_cases b <;> simp [pt])
  have h1 : ∀ i j : Fin N, ev (n := 1) ![pt S N 0, 0]
      (pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j)) = if j = i then 1 else 0 := by
    intro i j
    have hp : pderiv S ((1 : Fin 2), i) (ReciprocityTheory.ChartRestriction.G.TB.MV.addF S N j) =
        if j = i then (1 : PS S 2 N) else 0 := by
      by_cases h : j = i
      · subst h
        simp [ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply]
      · simp [ReciprocityTheory.ChartRestriction.G.TB.MV.addF, pderiv_X, Pi.single_apply, h]
    rw [hp, ev, ← coe_substAlgHom hs]
    split_ifs
    · exact map_one _
    · exact map_zero _
  simp only [Dof, h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpTieAlg
