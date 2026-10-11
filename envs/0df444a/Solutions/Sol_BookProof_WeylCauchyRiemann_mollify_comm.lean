-- Prove2me | solution 1 for BookProof.WeylCauchyRiemann.mollify_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T17:21:41.390992+00:00
-- url     : https://prove2.me/submissions/cf9b9727-3956-486d-b292-0eafea7ed227

-- Generated from ChapterWeylCauchyRiemann.lean — solution of BookProof.WeylCauchyRiemann.mollify_comm
import Mathlib
import Definitions.Def_ChapterWeylCauchyRiemann
import Definitions.Def_ChapterRadialMollifier
open BookProof.WeylCauchyRiemann




open MeasureTheory Metric Set Filter Complex BookProof.RadialMollifier
open scoped Convolution Topology ContDiff

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {F : ℂ → ℂ} (hF : Integrable F) {χ₁ χ₂ : ℂ → ℝ}
    (hχ₁ : Continuous χ₁) (hχ₁c : HasCompactSupport χ₁)
    (hχ₂ : Continuous χ₂) (hχ₂c : HasCompactSupport χ₂) :
    mollify (mollify F χ₁) χ₂ = mollify (mollify F χ₂) χ₁ := by

  have hprod : ∀ (a b : ℂ → ℝ), Continuous a → HasCompactSupport a → Continuous b →
      HasCompactSupport b → ∀ z : ℂ, Integrable
        (fun p : ℂ × ℂ => ((b (z - p.1) : ℂ) * (a (p.1 - p.2) : ℂ)) * F p.2)
        (volume.prod volume) := by
    intro a b ha hac hb hbc z
    obtain ⟨Ma, hMa⟩ := ha.bounded_above_of_compact_support hac
    obtain ⟨Mb, hMb⟩ := hb.bounded_above_of_compact_support hbc
    have hMa0 : 0 ≤ Ma := le_trans (norm_nonneg _) (hMa 0)
    have hMb0 : 0 ≤ Mb := le_trans (norm_nonneg _) (hMb 0)
    set K : Set ℂ := (fun v : ℂ => z - v) '' (tsupport b) with hK
    have hKc : IsCompact K := hbc.isCompact.image (by fun_prop)
    have hmeasK : MeasurableSet K := hKc.isClosed.measurableSet
    have hindint : Integrable (K.indicator (fun _ : ℂ => (Mb * Ma : ℝ))) :=
      (integrable_indicator_iff hmeasK).2
        (integrableOn_const (C := Mb * Ma) (ne_of_lt hKc.measure_lt_top))
    refine Integrable.mono' (hindint.mul_prod hF.norm) ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ hF.aestronglyMeasurable.comp_snd
      exact ((Complex.continuous_ofReal.comp
          (hb.comp (continuous_const.sub continuous_fst))).mul
        (Complex.continuous_ofReal.comp
          (ha.comp (continuous_fst.sub continuous_snd)))).aestronglyMeasurable
    · filter_upwards with p
      by_cases hp : p.1 ∈ K
      · rw [Set.indicator_of_mem hp]
        have hle : ‖b (z - p.1)‖ * ‖a (p.1 - p.2)‖ ≤ Mb * Ma :=
          mul_le_mul (hMb _) (hMa _) (norm_nonneg _) hMb0
        simp only [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      · have hb0 : b (z - p.1) = 0 := by
          by_contra hne
          exact hp ⟨z - p.1, subset_tsupport b hne, by ring⟩
        simp only [hb0, Complex.ofReal_zero, zero_mul, norm_zero]
        exact mul_nonneg (Set.indicator_apply_nonneg fun _ => mul_nonneg hMb0 hMa0)
          (norm_nonneg _)
  funext z
  have hstep : ∀ (a b : ℂ → ℝ), Continuous a → HasCompactSupport a → Continuous b →
      HasCompactSupport b →
      mollify (mollify F a) b z
        = ∫ w : ℂ, ∫ v : ℂ, ((b (z - v) : ℂ) * (a (v - w) : ℂ)) * F w := by
    intro a b ha hac hb hbc
    have h1 : mollify (mollify F a) b z
        = ∫ v : ℂ, ∫ w : ℂ, ((b (z - v) : ℂ) * (a (v - w) : ℂ)) * F w := by
      simp only [mollify]
      congr 1
      funext v
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext w
      ring
    rw [h1, integral_integral_swap (hprod a b ha hac hb hbc z)]
  rw [hstep χ₁ χ₂ hχ₁ hχ₁c hχ₂ hχ₂c, hstep χ₂ χ₁ hχ₂ hχ₂c hχ₁ hχ₁c]
  congr 1
  funext w
  have := integral_sub_left_eq_self
    (fun v : ℂ => ((χ₂ (z - v) : ℂ) * (χ₁ (v - w) : ℂ)) * F w) volume (z + w)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [show z - (z + w - v) = v - w by ring, show z + w - v - w = z - v by ring]
  ring
