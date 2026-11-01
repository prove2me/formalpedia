-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_postpayment_intrinsic_source_dividend_mark_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:42:32.119731+00:00
-- url     : https://prove2.me/submissions/9cc4956c-0852-488d-ace9-cbc968348ee1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_postpayment_reserve_exact_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The original postpayment jump measure carries source jumps with the
simultaneous dividend right atom subtracted from each mark. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (x + X.X u ω - rightLimit D u ω) -
          Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u))) =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧
        ((X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω)) ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) -
          (rightLimit D u ω - D u ω)))) := by
  let jP : ℝ≥0 → ℝ := fun u =>
    (x + X.X u ω - rightLimit D u ω) -
      Function.leftLim
        (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u
  let jX : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let jD : ℝ≥0 → ℝ := fun u => rightLimit D u ω - D u ω
  let jAlt : ℝ≥0 → ℝ := fun u => jX u - jD u
  change ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ jP u ≠ 0}).map
    (fun u : ℝ≥0 => (u, jP u))) =
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ jAlt u ≠ 0}).map
      (fun u : ℝ≥0 => (u, jAlt u)))
  have hj (u : ℝ≥0) (hu : 0 < u) : jP u = jAlt u := by
    exact avram_wave4_p2_original_postpayment_reserve_exact_jumpmark
      X x D hD ω u hu
  have hJX : Measurable jX := by
    exact (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp
      (Measurable.prodMk measurable_id measurable_const)
  have hReal : Set.Countable {t : ℝ |
      0 ≤ t ∧ rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} :=
    dividendStrategy_rightJump_support_countable D hD ω
  have hDCount : Set.Countable {u : ℝ≥0 | jD u ≠ 0} := by
    apply (hReal.image Real.toNNReal).mono
    intro u hu
    refine ⟨(u : ℝ), ?_, ?_⟩
    · constructor
      · exact NNReal.coe_nonneg u
      · have hne : rightLimit D u ω ≠ D u ω := by
          exact sub_ne_zero.mp hu
        simpa using hne
    · simp
  have hAltException :
      {u : ℝ≥0 | jX u ≠ jAlt u} ⊆ {u : ℝ≥0 | jD u ≠ 0} := by
    intro u hu
    by_contra hz
    have hzero : jD u = 0 := not_ne_iff.mp hz
    exact hu (by simp [jAlt, hzero])
  have hJAlt : Measurable jAlt :=
    hJX.measurable_of_countable_ne (hDCount.mono hAltException)
  have hPException :
      {u : ℝ≥0 | jAlt u ≠ jP u} ⊆ {(0 : ℝ≥0)} := by
    intro u hu
    by_cases hz : u = 0
    · simp [hz]
    · exfalso
      have hpos : (0 : ℝ≥0) < u :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ u) (Ne.symm hz)
      exact hu (hj u hpos).symm
  have hJP : Measurable jP :=
    hJAlt.measurable_of_countable_ne
      ((Set.countable_singleton (0 : ℝ≥0)).mono hPException)
  have hFP : Measurable (fun u : ℝ≥0 => (u, jP u)) :=
    Measurable.prodMk measurable_id hJP
  have hFA : Measurable (fun u : ℝ≥0 => (u, jAlt u)) :=
    Measurable.prodMk measurable_id hJAlt
  have hInter (E : Set (ℝ≥0 × ℝ)) :
      (fun u : ℝ≥0 => (u, jP u)) ⁻¹' E ∩
        {u : ℝ≥0 | 0 < u ∧ jP u ≠ 0} =
      (fun u : ℝ≥0 => (u, jAlt u)) ⁻¹' E ∩
        {u : ℝ≥0 | 0 < u ∧ jAlt u ≠ 0} := by
    ext u
    by_cases hu : 0 < u
    · simp only [Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_setOf_eq, hu, true_and]
      rw [hj u hu]
    · simp [hu]
  ext E hE
  rw [Measure.map_apply hFP hE, Measure.map_apply hFA hE]
  rw [Measure.restrict_apply (hE.preimage hFP),
      Measure.restrict_apply (hE.preimage hFA)]
  rw [hInter E]
