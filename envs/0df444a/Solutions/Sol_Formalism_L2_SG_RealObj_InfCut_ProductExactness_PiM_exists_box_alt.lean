-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.exists_box_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:19:36.460808+00:00
-- url     : https://prove2.me/submissions/9535f197-22de-4c15-b54c-cac3260e53eb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_ExistsBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (hne : ∀ i, μ i ≠ 0) :
    ∃ S : ∀ i, Set (α i), (∀ i, MeasurableSet (S i)) ∧ (∀ i, μ i (S i) ≠ 0) ∧ ∀ i, μ i (S i) ≠ ∞ := by
  have key : ∀ i, ∃ s : Set (α i), MeasurableSet s ∧ μ i s ≠ 0 ∧ μ i s ≠ ∞ := by
    intro i
    by_contra hc
    push_neg at hc
    apply hne i
    have hz : ∀ n, μ i (spanningSets (μ i) n) = 0 := fun n => by
      by_contra h0
      exact (measure_spanningSets_lt_top (μ i) n).ne (hc _ (measurableSet_spanningSets _ n) h0)
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ i)]
    exact measure_iUnion_null hz
  choose S hS1 hS2 hS3 using key
  exact ⟨S, hS1, hS2, hS3⟩
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
