-- Prove2me | solution 1 for Formalism.L2.Th1.B.Cor.first_jet_of_formal_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:02.443385+00:00
-- url     : https://prove2.me/submissions/81e37ac3-acb8-472f-a15b-e5ee9d72ea91

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_SigmaOneCocycleShifted
import Theorems.Thm_Formalism_L2_Th1_B_Cor_cc_Dinv
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_one_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Cor
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
namespace Formalism.L2.Th1.B.Cor
theorem _root_.solution : JetOne := by
  intro K _ _ _ l i f hl0 hl1 hi hS
  obtain ⟨hi0, -, hil⟩ := hi
  obtain ⟨hg0, hE⟩ := hS
  have hi1 : PowerSeries.coeff 1 i = -1 := by
    have e := law_coeff_one_subst l i hi0
    rw [hil, map_neg, hl1, one_mul] at e
    exact e.symm
  have hE1 : PowerSeries.coeff 1
      (PowerSeries.subst (PowerSeries.subst i f - f : PowerSeries K) (PowerSeries.exp K) :
        PowerSeries K) = PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K) := by
    rw [law_coeff_one_subst _ _ hg0, PowerSeries.coeff_exp]
    simp
  have hn : ‖PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K)‖ ≤ 1 := by
    rw [← hE1]
    exact hE (Finsupp.single () 1)
  rw [map_sub, law_coeff_one_subst f i hi0, hi1] at hn
  rw [cc_Dinv l f hl1, ← norm_neg]
  have : -(2 * PowerSeries.coeff 1 f) = PowerSeries.coeff 1 f * -1 - PowerSeries.coeff 1 f := by
    ring
  rw [this]
  exact hn
end Formalism.L2.Th1.B.Cor
