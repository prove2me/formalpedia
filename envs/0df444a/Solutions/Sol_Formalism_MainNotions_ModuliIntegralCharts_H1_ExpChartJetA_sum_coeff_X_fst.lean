-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.sum_coeff_X_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:03.583532+00:00
-- url     : https://prove2.me/submissions/4db6f4b7-a22e-4474-8a3f-9c1ef6330038

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
theorem _root_.solution {κ₁ κ₂ : Type} [Fintype κ₂] [DecidableEq κ₁] [DecidableEq κ₂] (u : κ₂ → R) (i : κ₁)
    (s : κ₁ × κ₂) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single (i, j) 1) (MvPowerSeries.X s : MvPowerSeries (κ₁ × κ₂) R) =
      if i = s.1 then u s.2 else 0 := by
  obtain ⟨s1, s2⟩ := s
  dsimp only
  by_cases hi : i = s1
  · subst hi
    rw [if_pos rfl, Finset.sum_eq_single s2]
    · simp [MvPowerSeries.coeff_X]
    · intro j _ hj
      simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hj]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj, hi]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
