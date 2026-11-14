-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:32.56882+00:00
-- url     : https://prove2.me/submissions/ca3a71ef-551a-47ca-9eb6-fdff78cf3dee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Current-checker revalidated original finite-cap BV source full-negative-jump HJB boundary proof from explicit Lipschitz and integrable negative mark premises. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε L M K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hεc : ε ≤ C.toReal)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * M ≤ K * (ε / 2))
    (hBound : ∀ r ∈ Icc (0 : ℝ) C.toReal, |w r| ≤ M)
    (hLip : ∀ a ∈ Icc (ε / 2) C.toReal,
      ∀ b ∈ Icc (ε / 2) C.toReal,
      |w a - w b| ≤ L * |a - b|)
    (y : ℕ → ℝ)
    (hy : Tendsto y atTop (𝓝 C.toReal))
    (hyInside : ∀ n, 0 < y n ∧ ENNReal.ofReal (y n) < C)
    (hyBand : ∀ n, y n ∈ Icc ε C.toReal)
    (hMeas : ∀ n, AEStronglyMeasurable
      (fun z : ℝ => w (y n + z) - w (y n))
      (X.ν.restrict (Iio (0 : ℝ)))) :
    X.drift + (∫ z in Iio (0 : ℝ),
      w (C.toReal + z) - w C.toReal ∂X.ν)
      - q * w C.toReal ≤ 0 := by
  let g : ℝ → ℝ := fun z =>
    if -(ε / 2) ≤ z then L * |z| else 2 * M
  have hg : Integrable g (X.ν.restrict (Iio (0 : ℝ))) :=
    avram_bva_capHJB42_original_full_negative_mark_envelope_integrable
      X hBV ε L M K hε hε2 hL hM hK hKL hKM
  have hDom : ∀ n, ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      ‖w (y n + z) - w (y n)‖ ≤ ‖g z‖ := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    exact avram_bva_capHJB41_original_full_negative_mark_small_big_envelope
      w C.toReal ε L M hε hεc hL hM hwNeg
      hBound hLip (y n) z (hyBand n) hz
  exact avram_bva_capHJB40_original_BV_true_closed_cap_HJB_from_full_mark_envelope
    X hStanding hBV q w C hC hFinite hwCont hwNeg
    hwGen hwGrad y hy hyInside g hg hMeas hDom
