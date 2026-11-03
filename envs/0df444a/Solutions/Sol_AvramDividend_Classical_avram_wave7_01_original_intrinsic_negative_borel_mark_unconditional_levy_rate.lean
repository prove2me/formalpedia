-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:32:59.230573+00:00
-- url     : https://prove2.me/submissions/4e261f11-995e-4b3b-8b5f-9d6fa2bd7603
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exact original infinite-activity marked rate reduces to true separated
negative Borel mark rates by canonical monotone exhaustion. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let a : ℕ → ℝ := fun n => -(ε n)
  let bands : ℕ → Set ℝ := fun n => B ∩ Iic (a n)
  have hεpos (n : ℕ) : 0 < ε n := by
    dsimp [ε]
    positivity
  have hεmono : Antitone ε := by
    intro i j hij
    dsimp [ε]
    have hpos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hle : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      have hijReal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    exact one_div_le_one_div_of_le hpos hle
  have hεzero : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hazero : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    simpa only [a, neg_zero] using hεzero.neg
  have hBm (n : ℕ) : MeasurableSet (bands n) :=
    hB.inter measurableSet_Iic
  have hMono : Monotone bands := by
    intro i j hij y hy
    exact ⟨hy.1, le_trans hy.2 (neg_le_neg (hεmono hij))⟩
  have hCover : (⋃ n, bands n) = B := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
      exact hn.1
    · intro hy
      have hyNeg : y < (0 : ℝ) := hBneg hy
      have hN : Ioi y ∈ 𝓝 (0 : ℝ) := isOpen_Ioi.mem_nhds hyNeg
      obtain ⟨n, hn⟩ := (hazero.eventually hN).exists
      exact Set.mem_iUnion.mpr ⟨n, ⟨hy, le_of_lt hn⟩⟩
  have hSep (n : ℕ) :
      ∃ δ : ℝ, 0 < δ ∧ bands n ⊆ Iic (-δ) := by
    exact ⟨ε n, hεpos n, fun y hy => hy.2⟩
  have hRates (n : ℕ) :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ bands n) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (bands n) := by
    exact avram_wave7_01_original_strict_separated_negative_borel_mark_levy_rate
      X s t hst (bands n) (hBm n) (ε n) (hεpos n)
        (fun y hy => hy.2)
  exact avram_wave7_01_source_borel_rate_from_separated_monotone_bands
    X s t hst B bands hBm hMono hCover hSep hRates
