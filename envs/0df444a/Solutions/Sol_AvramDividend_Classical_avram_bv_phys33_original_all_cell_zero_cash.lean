-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys33_original_all_cell_zero_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:26:28.71084+00:00
-- url     : https://prove2.me/submissions/88b087c2-1ce0-46cd-b177-09c3d64bd6e5

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
/-- On the original finite-activity BV path, every zero-reserve, source-jump-free
    physical cell has the exact drift-weighted Stieltjes cash ledger. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H)
    (u : ℕ → ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n i : ℕ,
      u n i ≤ u n (i + 1) →
      u n (i + 1) ≤ H →
      (∀ v : ℝ≥0, u n i ≤ v → v ≤ u n (i + 1) →
        riskProcess X x D v ω -
          (rightLimit D v ω - D v ω) = 0) →
      (∀ v : ℝ≥0, v ∈ Ioc (u n i) (u n (i + 1)) →
        X.X v ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) v = 0) →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc ((u n i : ℝ≥0) : ℝ) ((u n (i + 1) : ℝ≥0) : ℝ),
            f t ∂(dividendMeasure D ω)) =
        (∫⁻ t in Ioc ((u n i : ℝ≥0) : ℝ) ((u n (i + 1) : ℝ≥0) : ℝ),
            f t ∂((ENNReal.ofReal X.drift) • volume)) := by
  have hcash :=
    avram_bv_zero13_original_all_pathwise_restart_zero_weighted_cash_no_survival
      X hBV hFinite hDrift x C D hD H hH
  filter_upwards [hcash] with ω hω
  intro n i hmono hbound hzero hnojump f
  exact hω (u n i) (u n (i + 1)) hmono hbound hzero hnojump f
