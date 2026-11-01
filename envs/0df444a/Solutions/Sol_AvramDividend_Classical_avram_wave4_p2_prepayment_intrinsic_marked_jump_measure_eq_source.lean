-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:07:42.524835+00:00
-- url     : https://prove2.me/submissions/f82ee1ff-42d6-411a-b337-4248f9c053b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ riskProcess X x D u ω -
        Function.leftLim
          (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        riskProcess X x D u ω -
          Function.leftLim
            (fun v : ℝ≥0 => riskProcess X x D v ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
  let jU : ℝ≥0 → ℝ := fun u =>
    riskProcess X x D u ω -
      Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u
  let jX : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ jU u ≠ 0}).map
    (fun u : ℝ≥0 => (u, jU u))) =
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ jX u ≠ 0}).map
      (fun u : ℝ≥0 => (u, jX u)))
  have hj (u : ℝ≥0) (hu : 0 < u) : jU u = jX u :=
    avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
      X x D hD ω u hu
  have hJX : Measurable jX := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hUeq : jU = (fun u => if u = 0 then jU 0 else jX u) := by
    funext u
    by_cases h0 : u = 0
    · simp [h0]
    · have hu : (0 : ℝ≥0) < u :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ u) (Ne.symm h0)
      simp only [if_neg h0]
      exact hj u hu
  have hJU : Measurable jU := by
    rw [hUeq]
    exact measurable_const.ite
      (measurableSet_singleton (0 : ℝ≥0)) hJX
  have hFU : Measurable (fun u : ℝ≥0 => (u, jU u)) :=
    Measurable.prodMk measurable_id hJU
  have hFX : Measurable (fun u : ℝ≥0 => (u, jX u)) :=
    Measurable.prodMk measurable_id hJX
  have hInter (E : Set (ℝ≥0 × ℝ)) :
      (fun u : ℝ≥0 => (u, jU u)) ⁻¹' E ∩
        {u : ℝ≥0 | 0 < u ∧ jU u ≠ 0} =
      (fun u : ℝ≥0 => (u, jX u)) ⁻¹' E ∩
        {u : ℝ≥0 | 0 < u ∧ jX u ≠ 0} := by
    ext u
    by_cases hu : 0 < u
    · simp only [Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq, hu, true_and]
      rw [hj u hu]
    · simp [hu]
  ext E hE
  rw [Measure.map_apply hFU hE, Measure.map_apply hFX hE]
  rw [Measure.restrict_apply (hE.preimage hFU),
      Measure.restrict_apply (hE.preimage hFX)]
  rw [hInter E]
