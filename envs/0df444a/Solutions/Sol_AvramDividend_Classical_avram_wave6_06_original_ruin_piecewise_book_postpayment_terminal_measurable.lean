-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:30:25.453674+00:00
-- url     : https://prove2.me/submissions/b9814972-6348-4c0f-b8ed-f2a202deb2a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) : Measurable W := by
  have hτNN : Measurable τ :=
    measurable_coe_nnreal_ennreal_iff.mp hτ.measurable'
  have hτENN : Measurable (fun ω : Ω => (τ ω : ℝ≥0∞)) := hτ.measurable'
  have hPre : MeasurableSet {ω : Ω | τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω} :=
    (hτNN (measurableSet_singleton 0)).union
      (measurableSet_lt hτENN (ruinTime_measurable X x D hD))
  have hUplus : Measurable (fun ω : Ω =>
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω) :=
    avram_wave6_06_original_rightcont_stopped_postPayment_reserve_measurable
      X x D hD τ hτ
  have hXτ : Measurable (fun ω : Ω => X.X (τ ω) ω) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (hτNN.prodMk measurable_id)
  have hDplusLeftτ : Measurable (fun ω : Ω =>
      Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω)) :=
    (avram_wave6_06_original_prepayment_dividend_leftLimit_joint_measurable D hD).comp
      (hτNN.prodMk measurable_id)
  have hDbookRep : Measurable (fun ω : Ω =>
      if τ ω = 0 then (0 : ℝ)
      else Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω)) :=
    Measurable.ite (hτNN (measurableSet_singleton 0))
      measurable_const hDplusLeftτ
  have hBookRep : Measurable (fun ω : Ω =>
      x + X.X (τ ω) ω -
        (if τ ω = 0 then (0 : ℝ)
         else Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω))) :=
    (measurable_const.add hXτ).sub hDbookRep
  have hRep : Measurable (fun ω : Ω =>
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else x + X.X (τ ω) ω -
        (if τ ω = 0 then (0 : ℝ)
         else Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω))) :=
    Measurable.ite hPre hUplus hBookRep
  have heq : W = (fun ω : Ω =>
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else x + X.X (τ ω) ω -
        (if τ ω = 0 then (0 : ℝ)
         else Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω))) := by
    funext ω
    rw [hW ω]
    by_cases hp : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · simp [hp]
    · have hne : τ ω ≠ 0 := fun hz => hp (Or.inl hz)
      have ht : 0 < τ ω := pos_iff_ne_zero.mpr hne
      haveI : (𝓝[<] (τ ω)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
      have hleft :
          Function.leftLim (fun s : ℝ≥0 => rightLimit D s ω) (τ ω) =
            D (τ ω) ω :=
        leftLim_eq_of_tendsto
          (avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD ω (τ ω) ht)
      simp [hp, hne, hleft, riskProcess]
  rw [heq]
  exact hRep
