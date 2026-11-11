-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise41_original_dyadic_physical_mark_count_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T19:47:18.507053+00:00
-- url     : https://prove2.me/submissions/77d1f886-a200-49ac-ae6c-9ec5fe0999cf

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_anoise45_original_band_finite_jump_count_ledger
import Theorems.Thm_AvramDividend_Classical_avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- The finite physical jump ledger and elementary dyadic mark convergence
    establish original-space marked count convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hInt : ∀ n : ℕ, ∀ T : ℝ≥0, Integrable
      (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      (∀ᵐ ω ∂P, Tendsto
        (fun k => ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) * (J k i ω).toReal)
        atTop
        (𝓝 ((avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω -
            avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) +
          (((t - s : ℝ≥0) : ℝ) *
            (∫ z in B, z ∂X.ν))))) := by
  classical
  intro n s t hst
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let C : ℕ → ℕ → Set ℝ := fun k i =>
    B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
      (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
  let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ C k i)
  dsimp only
  filter_upwards [] with ω
  obtain ⟨F, hF, hCount, hSource⟩ :=
    avram_anoise45_original_band_finite_jump_count_ledger X n s t hst ω
  have hFiniteMark :=
    avram_anoise46_finite_dyadic_mark_endpoint_weighted_convergence
      n F (fun u => X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) hF
  convert hFiniteMark using 1
  · ext k
    apply Finset.sum_congr rfl
    intro i hi
    have hCountReal : (J k i ω).toReal =
        ((F.filter (fun u => X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ C k i)).card : ℝ) := by
      have hh := congrArg ENNReal.toReal (hCount k i)
      simpa [J, C, B] using hh
    exact congrArg (fun v : ℝ => (-1 + (i : ℝ) / (2 : ℝ) ^ k) * v) hCountReal
  · exact congrArg (𝓝) hSource
