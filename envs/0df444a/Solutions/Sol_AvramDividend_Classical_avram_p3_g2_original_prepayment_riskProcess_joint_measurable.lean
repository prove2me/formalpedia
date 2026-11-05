-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_prepayment_riskProcess_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:10:27.928241+00:00
-- url     : https://prove2.me/submissions/fa4f5daf-895c-46db-9ddb-c4076db4cd63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original prepayment reserve jointly measurable, keeping the D₀ atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    Measurable (fun z : ℝ≥0 × Ω => riskProcess X x D z.1 z.2) := by
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    rightContinuous_measurable_sections_joint_evaluation X.X
      (fun t => (X.adapted t).mono (𝓕.le t) le_rfl) X.rightCont
  have hLeft : Measurable (fun z : ℝ≥0 × Ω =>
      Function.leftLim (fun s : ℝ≥0 => rightLimit D s z.2) z.1) :=
    avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable D hD
  have hDzero : Measurable (fun ω : Ω => D 0 ω) :=
    hD.2.2.2.measurable
  have hDzeroProd : Measurable (fun z : ℝ≥0 × Ω => D 0 z.2) :=
    hDzero.comp measurable_snd
  have hzSet : MeasurableSet {z : ℝ≥0 × Ω | z.1 = 0} :=
    (measurableSet_singleton (0 : ℝ≥0)).preimage measurable_fst
  have hPiece : Measurable (fun z : ℝ≥0 × Ω =>
      if z.1 = 0 then D 0 z.2 else
        Function.leftLim (fun s : ℝ≥0 => rightLimit D s z.2) z.1) :=
    hDzeroProd.ite hzSet hLeft
  have heq : (fun z : ℝ≥0 × Ω => D z.1 z.2) =
      (fun z : ℝ≥0 × Ω => if z.1 = 0 then D 0 z.2 else
        Function.leftLim (fun s : ℝ≥0 => rightLimit D s z.2) z.1) := by
    funext z
    by_cases hz : z.1 = 0
    · simp [hz]
    · have ht : 0 < z.1 := pos_iff_ne_zero.mpr hz
      haveI : (𝓝[<] z.1).NeBot :=
        nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
      have hlim :=
        avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD z.2 z.1 ht
      have hleftEq : Function.leftLim
          (fun s : ℝ≥0 => rightLimit D s z.2) z.1 = D z.1 z.2 :=
        leftLim_eq_of_tendsto hlim
      simp [hz, hleftEq]
  have hDjoint : Measurable (fun z : ℝ≥0 × Ω => D z.1 z.2) := by
    rw [heq]
    exact hPiece
  change Measurable (fun z : ℝ≥0 × Ω =>
    x + X.X z.1 z.2 - D z.1 z.2)
  exact (measurable_const.add hX).sub hDjoint
