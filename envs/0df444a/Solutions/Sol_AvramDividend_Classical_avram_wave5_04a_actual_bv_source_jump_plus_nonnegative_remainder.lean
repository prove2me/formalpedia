-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_jump_plus_nonnegative_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:48:51.070462+00:00
-- url     : https://prove2.me/submissions/3e3d181b-af86-4a08-bb3a-26f89d743540

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical

/--
On one actual-source BV event, the stopped Stieltjes loss is the sum of
all original negative source-jump magnitudes and an explicitly
nonnegative remainder. The remainder is permitted to contain diffuse
finite variation, so no pure-jump identity is assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ F : StieltjesFunction ℝ≥0,
      (∀ t : ℝ≥0, (F t : ℝ) = (t : ℝ) * X.drift - X.X t ω) ∧
      ∀ (s t : ℝ≥0), s ≤ t →
        ∃ r : ℝ≥0∞,
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ∈ Ioc s t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0) + r = F.measure (Ioc s t) := by
  filter_upwards
    [avram_wave4_04a_bv_actual_jump_atomic_domination_all_measurable_time_sets X hBV]
    with ω hω
  obtain ⟨F, hF, hdom⟩ := hω
  refine ⟨F, hF, ?_⟩
  intro s t hst
  let jumpMass : ℝ≥0∞ :=
    ∑' (u : ℝ≥0),
      if 0 < u ∧ u ∈ Ioc s t then
        ENNReal.ofReal (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
      else 0
  have hbound : jumpMass ≤ F.measure (Ioc s t) := by
    convert (hdom (Ioc s t) measurableSet_Ioc) using 1
    dsimp [jumpMass]
    apply tsum_congr
    intro u
    by_cases hu : 0 < u ∧ u ∈ Ioc s t
    · simp [hu]
    · simp [hu]
  refine ⟨F.measure (Ioc s t) - jumpMass, ?_⟩
  change jumpMass + (F.measure (Ioc s t) - jumpMass) =
    F.measure (Ioc s t)
  rw [add_comm]
  exact tsub_add_cancel_of_le hbound
