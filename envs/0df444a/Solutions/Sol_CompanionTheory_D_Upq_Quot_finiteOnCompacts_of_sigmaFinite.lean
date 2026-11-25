-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.finiteOnCompacts_of_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:02:37.720514+00:00
-- url     : https://prove2.me/submissions/693a5ae7-f6ad-4434-8207-839863a1167a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_Exists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace Set
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H]
namespace CompanionTheory.D.Upq.Quot
theorem _root_.solution (η : Measure H) [SigmaFinite η] [IsMulLeftInvariant η] :
    IsFiniteMeasureOnCompacts η := by
  have K : PositiveCompacts H := Classical.arbitrary _
  have h := haarMeasure_unique η K
  have hK : η K ≠ ∞ := fun hK => by
    rw [hK] at h
    have h1 : ∀ n, haarMeasure K (spanningSets η n) = 0 := fun n => by
      by_contra hn
      have := measure_spanningSets_lt_top η n
      rw [show η (spanningSets η n) = (∞ • haarMeasure K) (spanningSets η n) by rw [← h],
        Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at this
      exact lt_irrefl _ this
    have h2 := measure_iUnion_null h1
    rw [iUnion_spanningSets, measure_univ_eq_zero] at h2
    exact NeZero.ne _ h2
  refine ⟨fun L hL => ?_⟩
  rw [h, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top hK.lt_top hL.measure_lt_top
end CompanionTheory.D.Upq.Quot
