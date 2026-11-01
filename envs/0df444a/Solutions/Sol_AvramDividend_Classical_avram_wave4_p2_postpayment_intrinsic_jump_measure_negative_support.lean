-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_jump_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:09:40.520003+00:00
-- url     : https://prove2.me/submissions/1ae63f16-5b68-4d17-afb8-fdac894c349f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The actual postpayment intrinsic jump measure puts no mass on
nonnegative marks: source Lévy jumps and simultaneous dividend atoms
both move the controlled reserve downwards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)))
      (Ioc s t ×ˢ Ici (0 : ℝ)) = 0 := by
  rw [avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
    X x D hD ω]
  let j : ℝ≥0 → ℝ := fun u =>
    (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
      (rightLimit D u ω - D u ω)
  let jMasked : ℝ≥0 → ℝ := fun u => if 0 < u then j u else 0
  have hMasked : Measurable jMasked := by
    exact (avram_wave4_p2_postpayment_combined_jumpmark_joint_measurable
      X x D hD).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hException :
      {u : ℝ≥0 | jMasked u ≠ j u} ⊆ {(0 : ℝ≥0)} := by
    intro u hu
    by_cases hz : u = 0
    · simp [hz]
    · exfalso
      have hp : (0 : ℝ≥0) < u := pos_iff_ne_zero.mpr hz
      exact hu (by simp [jMasked, hp])
  have hj : Measurable j :=
    hMasked.measurable_of_countable_ne
      ((Set.countable_singleton (0 : ℝ≥0)).mono hException)
  have hF : Measurable (fun u : ℝ≥0 => (u, j u)) :=
    Measurable.prodMk measurable_id hj
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ j u ≠ 0}).map
    (fun u : ℝ≥0 => (u, j u))) (Ioc s t ×ˢ Ici (0 : ℝ)) = 0
  rw [Measure.map_apply hF (measurableSet_Ioc.prod measurableSet_Ici)]
  rw [Measure.restrict_apply
    ((measurableSet_Ioc.prod measurableSet_Ici).preimage hF)]
  have hempty :
      (fun u : ℝ≥0 => (u, j u)) ⁻¹' (Ioc s t ×ˢ Ici (0 : ℝ)) ∩
        {u : ℝ≥0 | 0 < u ∧ j u ≠ 0} = ∅ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod,
      Set.mem_Ioc, Set.mem_Ici, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    intro hu
    rcases hu with ⟨huE, huS⟩
    have hu0 : 0 < u := huS.1
    have hne : j u ≠ 0 := huS.2
    have hge : 0 ≤ j u := huE.2
    have hX := avram_wave4_04a_actual_levy_jumpmark_nonpositive
      X ω u hu0
    have hDle := dividendStrategy_le_rightLimit D hD ω u
    have hle : j u ≤ 0 := by
      dsimp [j]
      linarith
    exact hne (le_antisymm hle hge)
  rw [hempty]
  simp
