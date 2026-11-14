-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB50_original_BV_full_cap_generator_sign_of_local_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:53:37.855999+00:00
-- url     : https://prove2.me/submissions/dc770d02-c7e2-4af3-92b7-d560a12dca63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Current-checker revalidated finite-cap original BV unmasked HJB source endpoint proof from HJB43 and HJB48. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε L K : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (hεc : ε ≤ C.toReal)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hKL : L ≤ K) (hKM : 2 * w C.toReal ≤ K * (ε / 2))
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
  obtain ⟨hwCap, hBound⟩ :=
    avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
      C hC hFinite w hwCont hw0 hwSmooth hwGrad
  exact avram_bva_capHJB43_original_BV_cap_sign_from_local_lipschitz
    X hStanding hBV q w C hC hFinite hwCont hwNeg
    hwGen hwGrad ε L (w C.toReal) K hε hε2 hεc
    hL hwCap hK hKL hKM hBound hLip
    y hy hyInside hyBand hMeas
