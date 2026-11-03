-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:38:21.788809+00:00
-- url     : https://prove2.me/submissions/b15ba8e4-0ad1-487c-a4b9-03da21c4506b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (H : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ S : ℝ≥0, S ≤ H →
        ∀ᵐ ω ∂P,
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            max 0 (Real.exp (-(q * (S : ℝ))) *
              w (x + X.X S ω - rightLimit D S ω))
          else 0) ≤ K := by
  classical
  have hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω := by
    intro ω
    change 0 ≤ ⨅ (s : Ioi (0 : ℝ≥0)), D s ω
    apply le_ciInf
    intro s
    calc
      0 = D 0 ω := (hD.1 ω).symm
      _ ≤ D s ω := hD.2.1 ω (le_of_lt s.property)
  let B : ℝ := max 0 (x + (H : ℝ) * X.drift)
  have hB0 : 0 ≤ B := le_max_left _ _
  obtain ⟨M, hM0, hM⟩ :=
    continuous_test_abs_le_on_finite_cap w B hB0 hw_cont
  refine ⟨M, hM0, ?_⟩
  intro S hSH
  have hCeiling : ∀ᵐ ω ∂P,
      x + X.X S ω - rightLimit D S ω ≤
        x + (S : ℝ) * X.drift :=
    avram_wave7_04_original_BV_postright_terminal_drift_ceiling_ae
      X hBV x D hD hInitial S
  filter_upwards [hCeiling] with ω hCeil
  by_cases hSurv : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hY0 : 0 ≤ x + X.X S ω - rightLimit D S ω :=
      postPaymentReserve_nonnegative_strictly_before_ruin
        X x D hD ω S hSurv
    have hDrift : 0 ≤ X.drift := le_of_lt (bv_standing_drift_pos X hX hBV).1
    have hSHreal : (S : ℝ) ≤ (H : ℝ) := by exact_mod_cast hSH
    have hYB : x + X.X S ω - rightLimit D S ω ≤ B := by
      calc
        x + X.X S ω - rightLimit D S ω ≤
            x + (S : ℝ) * X.drift := hCeil
        _ ≤ x + (H : ℝ) * X.drift :=
          add_le_add_right (mul_le_mul_of_nonneg_right hSHreal hDrift) x
        _ ≤ B := le_max_right _ _
    have hWUpper : w (x + X.X S ω - rightLimit D S ω) ≤ M :=
      (abs_le.mp (hM _ hY0 hYB)).2
    have hExpPos : 0 ≤ Real.exp (-(q * (S : ℝ))) := Real.exp_nonneg _
    have hExpLE : Real.exp (-(q * (S : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply neg_nonpos.mpr
      exact mul_nonneg (le_of_lt hq) (NNReal.coe_nonneg _)
    have hProduct : Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω) ≤ M := by
      calc
        _ ≤ Real.exp (-(q * (S : ℝ))) * M :=
          mul_le_mul_of_nonneg_left hWUpper hExpPos
        _ ≤ 1 * M := mul_le_mul_of_nonneg_right hExpLE hM0
        _ = M := one_mul M
    have hMax : max 0 (Real.exp (-(q * (S : ℝ))) *
        w (x + X.X S ω - rightLimit D S ω)) ≤ M :=
      max_le hM0 hProduct
    simpa only [if_pos hSurv] using hMax
  · simpa only [if_neg hSurv] using hM0
