-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_variable_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:12.852022+00:00
-- url     : https://prove2.me/submissions/c2ad7ac4-39d8-47db-9e62-e6dfd65cc7a1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
theorem _root_.solution {κ₁ κ₂ : Type} [Fintype κ₁] [DecidableEq κ₁] [Fintype κ₂] [DecidableEq κ₂] (h : κ₁ → κ₂ → R)
    (s : κ₁ × κ₂) :
    ∑ i, ∑ j, h i j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      h s.1 s.2 := by
  obtain ⟨s1, s2⟩ := s
  rw [Finset.sum_eq_single s1, Finset.sum_eq_single s2]
  · simp [MvPowerSeries.coeff_X]
  · intro j _ hj
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
  · simp
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]
  · simp
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
