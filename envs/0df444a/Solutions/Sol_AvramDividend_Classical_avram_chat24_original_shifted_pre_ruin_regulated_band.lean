-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_shifted_pre_ruin_regulated_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:05:16.920079+00:00
-- url     : https://prove2.me/submissions/49f56034-c197-425f-8606-86619496b234

import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

-- Original source envelope and left-limit argument; remote verification required.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (δ : ℝ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let b : ℝ := x + δ + T * X.drift
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + δ + X.X s p.2 - rightLimit D s p.2) p.1
    ∀ᵐ ω ∂P, ∀ B : ℝ≥0, B ≤ S → (B : ℝ≥0∞) < ruinTime X x D ω →
      (∀ s : ℝ≥0, s ≤ B → riskProcess X x D s ω + δ ∈ Icc δ b) ∧
      ∀ t : ℝ≥0, 0 < t → t ≤ B →
        Y (t, ω) ∈ Icc δ b ∧
        Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω + δ)
          (𝓝[<] t) (nhds (Y (t, ω))) := by
  intro S b Y
  have hd := (avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual X hX hBV).1
  filter_upwards [(avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual X hX hBV).2] with ω hω
  obtain ⟨R, hRdef, hRzero, hRmono, hR⟩ := hω
  intro B hBS hBruin
  have hreserve (s : ℝ≥0) (hs : s ≤ B) :
      riskProcess X x D s ω + δ ∈ Icc δ b := by
    have hsruin : (s : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_le_of_lt (by exact_mod_cast hs) hBruin
    have hnonneg : 0 ≤ riskProcess X x D s ω := by
      by_contra hn
      exact (not_le_of_gt hsruin)
        (iInf_le_of_le s (iInf_le _ (lt_of_not_ge hn)))
    have hD0 : 0 ≤ D s ω := by
      calc
        0 = D (0 : ℝ≥0) ω := (hD.1.1.1 ω).symm
        _ ≤ D s ω := hD.1.1.2.1 ω (show (0 : ℝ≥0) ≤ s from bot_le)
    obtain ⟨hRnonneg, hrepr⟩ := hR s
    have hXs : X.X s ω ≤ (s : ℝ) * X.drift := by
      rw [hrepr]
      exact (sub_le_self _ hRnonneg).trans (sub_le_self _ ENNReal.toReal_nonneg)
    have hsT : (s : ℝ) ≤ T := by exact_mod_cast hs.trans hBS
    have hmul := mul_le_mul_of_nonneg_right hsT hd.le
    constructor
    · linarith
    · dsimp only [riskProcess, b] at *
      linarith
  refine ⟨hreserve, ?_⟩
  intro t ht htB
  letI : (𝓝[<] t).NeBot := nhdsWithin_Iio_neBot' ⟨0, ht⟩ le_rfl
  obtain ⟨l, hl⟩ := X.leftLim ω t ht
  let r : ℝ := x + δ + l - D t ω
  have hDleft := (hD.1.1.2.2.1 ω t).mono (show Iio t ⊆ Iic t from fun s hs => show s ≤ t from le_of_lt hs)
  have hlift : Tendsto (fun s : ℝ≥0 => x + δ + X.X s ω)
      (𝓝[<] t) (nhds (x + δ + l)) := tendsto_const_nhds.add hl
  have hp : Tendsto (fun s : ℝ≥0 => riskProcess X x D s ω + δ)
      (𝓝[<] t) (nhds r) := by
    have heq (s : ℝ≥0) : riskProcess X x D s ω + δ =
        x + δ + X.X s ω - D s ω := by dsimp [riskProcess]; ring
    simpa only [heq] using hlift.sub hDleft.tendsto
  have hpost : Tendsto (fun s : ℝ≥0 => x + δ + X.X s ω - rightLimit D s ω)
      (𝓝[<] t) (nhds r) :=
    hlift.sub
      (avram_wave3_04_rightLimit_leftLimit_eq_dividend D hD.1.1 ω t ht)
  have hY : Y (t, ω) = r := leftLim_eq_of_tendsto hpost
  have hr : r ∈ Icc δ b := isClosed_Icc.mem_of_tendsto hp (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hreserve s (hs.le.trans htB))
  constructor
  · simpa only [hY] using hr
  · simpa only [hY] using hp
