-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:11:51.612443+00:00
-- url     : https://prove2.me/submissions/de6a4618-0368-4bff-b3a9-fac7ca670468

import Mathlib.Topology.Defs.Filter
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A candidate continuous on nonnegative reserves and identically zero
on negative reserves is uniformly bounded below any finite horizon ceiling. -/
theorem solution
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → ‖w v‖ ≤ R := by
  have hSub : Icc (0 : ℝ) b ⊆ Ici 0 := by
    intro v hv
    exact hv.1
  obtain ⟨R, hR⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_bound_of_continuousOn
      (hwCont.mono hSub)
  have hR0 : 0 ≤ R :=
    le_trans (norm_nonneg (w 0)) (hR 0 ⟨le_refl _, hb⟩)
  refine ⟨R, hR0, ?_⟩
  intro v hv
  by_cases hneg : v < 0
  · simpa [hwNeg v hneg] using hR0
  · exact hR v ⟨le_of_not_gt hneg, hv⟩
