-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T21:54:06.466623+00:00
-- url     : https://prove2.me/submissions/a10b3cb6-af9c-4687-bbaa-5ba7b990427d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (v : ℕ → ℝ≥0) (hv : Monotone v)
    (m : ℕ) (hPre : ∀ i < m,
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range m,
      ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v i : ℝ))) *
        (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by
  dsimp
  apply Finset.sum_nonpos
  intro i hi
  have hmono : v i ≤ v (i + 1) := hv (Nat.le_succ i)
  have hcontact := hPre i (Finset.mem_range.mp hi)
  exact avram_b240_original_ruinclipped_mixed_allcap_discounted_full_stieltjes_source_sign
    X x q hq C hC w hw_cont hw_smooth hw_grad D hD ω (v i) (v (i + 1))
    hmono hcontact
