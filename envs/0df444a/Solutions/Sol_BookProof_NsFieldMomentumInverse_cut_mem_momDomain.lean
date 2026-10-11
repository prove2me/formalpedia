-- Prove2me | solution 1 for BookProof.NsFieldMomentumInverse.cut_mem_momDomain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:44:49.584008+00:00
-- url     : https://prove2.me/submissions/c6e272d5-42a6-48a8-b444-07bdb5be9a02

-- Generated from ChapterNsFieldMomentumInverse.lean — solution of BookProof.NsFieldMomentumInverse.cut_mem_momDomain
import Mathlib
import Definitions.Def_ChapterNsFieldMomentumInverse
import Theorems.Thm_BookProof_NsFieldMomentumInverse_isMomInverse_of_memLp
import Theorems.Thm_BookProof_NsFieldMomentumInverse_coeFn_cut
import Definitions.Def_ChapterNsSpatialMomentumMultiplier
import Definitions.Def_ChapterFourierMultiplierEsa
import Definitions.Def_ChapterStrichartzWave
open BookProof.NsFieldMomentumInverse




open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

set_option maxHeartbeats 1000000 in
theorem solution {m : W} (hm : m ≠ 0) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) :
    cut m n f ∈ momDomain m := by

  have hmeas : AEStronglyMeasurable
      (fun ξ => (cut m n f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) (volume : Measure W) :=
    ((MeasureTheory.Lp.aestronglyMeasurable (cut m n f)).aemeasurable.div
      ((Complex.continuous_ofReal.comp
        (continuous_momSymbol m)).measurable.aemeasurable)).aestronglyMeasurable
  have hdom : MemLp (fun ξ => (((n : ℝ) + 1) : ℂ) * (f : W → ℂ) ξ) 2 (volume : Measure W) :=
    (MeasureTheory.Lp.memLp f).const_mul _
  have hbound : ∀ᵐ ξ ∂(volume : Measure W),
      ‖(cut m n f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)‖
        ≤ ‖(((n : ℝ) + 1) : ℂ) * (f : W → ℂ) ξ‖ := by
    filter_upwards [coeFn_cut m n f] with ξ hξ
    rw [hξ]
    by_cases hmem : ξ ∈ cutSet m n
    · have hlow : 1 / ((n : ℝ) + 1) ≤ |momSymbol m ξ| := hmem
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hσ : |momSymbol m ξ| ≠ 0 := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact ne_of_gt (lt_of_lt_of_le this hlow)
      rw [Set.indicator_of_mem hmem, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul]
      rw [div_le_iff₀ (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hσ))]
      have hn : ‖(((n : ℝ) + 1) : ℂ)‖ = (n : ℝ) + 1 := by
        have : (((n : ℝ) + 1) : ℂ) = ((((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      rw [hn]
      calc ‖(f : W → ℂ) ξ‖ = ‖(f : W → ℂ) ξ‖ * (((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) := by
            rw [mul_one_div_cancel (ne_of_gt hpos), mul_one]
        _ ≤ ‖(f : W → ℂ) ξ‖ * (((n : ℝ) + 1) * |momSymbol m ξ|) := by
            gcongr
        _ = ((n : ℝ) + 1) * ‖(f : W → ℂ) ξ‖ * |momSymbol m ξ| := by ring
    · rw [Set.indicator_of_notMem hmem]
      simp only [zero_div, norm_zero]
      positivity
  exact ⟨_, isMomInverse_of_memLp hm _ (hdom.of_le hmeas hbound)⟩
