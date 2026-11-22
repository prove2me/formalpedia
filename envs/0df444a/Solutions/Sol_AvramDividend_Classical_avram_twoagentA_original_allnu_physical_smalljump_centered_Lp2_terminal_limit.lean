-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_original_allnu_physical_smalljump_centered_Lp2_terminal_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:54:20.871107+00:00
-- url     : https://prove2.me/submissions/2a50ed1c-5a18-4336-9c17-ea19f7a0bf15

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let r : ℕ → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let F : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n,
        (-(1 / ((i : ℝ) + 1))) *
          ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    ∃ M : ℕ → Lp ℝ 2 P,
      (∀ n, (M n : Ω → ℝ) =ᵐ[P] F n) ∧
        ∃ L : Lp ℝ 2 P, Tendsto M atTop (𝓝 L) ∧
          (∫ ω, L ω ∂P) = 0 := by
  classical
  intro B NX r F
  obtain ⟨M, hM, L, hML⟩ :=
    avram_twoagentA_original_allnu_reciprocal_physical_compensated_Lp2_limit_exists X T
  have hMean (n : ℕ) : (∫ ω, (M n : Ω → ℝ) ω ∂P) = 0 := by
    have hSrc :=
      (avram_twoagentA_original_anynu_reciprocal_physical_partial_sum_L1_centered X T n).2
    calc
      (∫ ω, (M n : Ω → ℝ) ω ∂P) =
          (∫ ω, F n ω ∂P) := integral_congr_ae (hM n)
      _ = 0 := by simpa only [] using hSrc
  have hCauchy : CauchySeq M := hML.cauchySeq
  obtain ⟨L', hL', hZero⟩ :=
    avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
      X M hCauchy hMean
  exact ⟨M, hM, L', hL', hZero⟩
