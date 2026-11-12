-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b23_original_A_K_common_realtime_ae_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:46:43.37041+00:00
-- url     : https://prove2.me/submissions/732c32ca-ac7f-48b5-b0e0-40008c79ce97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_A_K_common_nat_pointwise_limit
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b23_original_real_horizon_away_ruin_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original frozen A and continuous K real-time coefficients share a finite-horizon almost-everywhere limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω)
    (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q T : ℝ) (hT : 0 < T)
    (hsource : ∀ r : ℝ≥0, (r : ℝ) ≤ T →
       X.X r ω = (r : ℝ) * X.drift) :
    let S : ℝ≥0 := ⟨T, hT.le⟩
    let τ : ℝ≥0∞ := ruinTime X x D ω
    let U : ℝ≥0 → ℝ := fun s => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) s
    let s : ℕ → ℝ → ℝ≥0 := fun n r => Real.toNNReal
      (T * (⌊((((Real.toNNReal r : ℝ≥0) : ℝ) / T) *
        ((n : ℝ) + 2))⌋₊ : ℝ) / ((n : ℝ) + 2))
    let F : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))) *
      ∫ z in Iio (0 : ℝ), w (U t + z) - w (U t) ∂X.ν
    let f : ℝ → ℝ := fun r =>
      if ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < τ ∧
         0 ≤ U (Real.toNNReal r) ∧
         ENNReal.ofReal (U (Real.toNNReal r)) ≤ C
      then F (Real.toNNReal r) else 0
    ∀ᵐ r ∂((volume : Measure ℝ).restrict (Icc 0 T)),
      (Tendsto (fun n : ℕ =>
        if (s n r : ℝ≥0∞) < τ ∧
          0 ≤ U (s n r) ∧ ENNReal.ofReal (U (s n r)) ≤ C
        then F (s n r) else 0) atTop (𝓝 (f r))) ∧
      (Tendsto (fun n : ℕ =>
        if 0 < Real.toNNReal r ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ) < T - T / ((n : ℝ) + 2) ∧
          ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≤ τ ∧
          0 ≤ U (Real.toNNReal r) ∧
          ENNReal.ofReal (U (Real.toNNReal r)) ≤ C
        then F (Real.toNNReal r) else 0) atTop (𝓝 (f r))) := by
  intro S τ U s F f
  have hae := avram_bvb_b23_original_real_horizon_away_ruin_ae T hT τ
  filter_upwards [hae] with r hr
  have hnonneg : 0 ≤ r := le_of_lt hr.1
  have hcast : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := by
    simp [Real.coe_toNNReal, hnonneg]
  have ht : Real.toNNReal r ≤ S := by
    apply NNReal.coe_le_coe.mp
    change (Real.toNNReal r : ℝ) ≤ T
    simpa only [hcast] using hr.2.1.le
  have htpos : 0 < Real.toNNReal r :=
    (Real.toNNReal_pos).2 hr.1
  have hnotruin : ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) ≠ τ := by
    simpa only [← ENNReal.ofReal_coe_nnreal, hcast] using hr.2.2
  have hTreal : ((Real.toNNReal r : ℝ≥0) : ℝ) < T := by
    simpa only [hcast] using hr.2.1
  have hsourceS : ∀ z : ℝ≥0, z ≤ S →
      X.X z ω = (z : ℝ) * X.drift := by
    intro z hz
    have hzR : (z : ℝ) ≤ (S : ℝ) := NNReal.coe_le_coe.mpr hz
    change (z : ℝ) ≤ T at hzR
    exact hsource z hzR
  have hp := avram_bvb_b23_original_A_K_common_nat_pointwise_limit
    X hX hBV x C hxc D hD ω S (Real.toNNReal r) ht htpos
    hnotruin hsourceS hFinite w hw_cont hw_neg hActivity q T hT hTreal
  simpa only [s, U, F, f, τ] using hp
