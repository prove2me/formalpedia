-- Prove2me | solution 1 for DbarRegularity.exists_contDiff_hasCompactSupport_eLpNorm_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:12:41.270029+00:00
-- url     : https://prove2.me/submissions/53456d33-95f5-4279-9d5b-8425c6d62dcc

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ENNReal Convolution

/-- Smooth compactly supported functions are dense in `L^p(ℝ^d; ℂ)`, `1 ≤ p < ∞`. -/
theorem exists_contDiff_hasCompactSupport_eLpNorm_sub_le {d : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f p volume) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h ∧
      eLpNorm (f - h) p volume ≤ ENNReal.ofReal δ := by
  obtain ⟨g, hgc, hfg, hgcont, hgmem⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp
    (ε := ENNReal.ofReal (δ / 2)) (by simp [hδ])
  set S : Set (EuclideanSpace ℝ (Fin d)) := cthickening 1 (tsupport g) with hS
  have hScpt : IsCompact S := hgc.isCompact.cthickening
  have hSm : MeasurableSet S := isClosed_cthickening.measurableSet
  have hSfin : volume S ≠ ∞ := hScpt.measure_lt_top.ne
  set X : ℝ≥0∞ := volume S ^ (1 / p.toReal) with hX
  have hXfin : X ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hSfin
  set c : ℝ := X.toReal
  set η : ℝ := δ / 2 / (c + 1) with hη
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hη0 : 0 < η := by positivity
  have hηc : η * c ≤ δ / 2 := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨r₀, hr₀, hunif⟩ := Metric.uniformContinuous_iff.1
    (hgc.uniformContinuous_of_continuous hgcont) η hη0
  set r : ℝ := min r₀ 1 with hr
  have hr0 : 0 < r := lt_min hr₀ one_pos
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  set h : EuclideanSpace ℝ (Fin d) → ℂ := φ.normed volume ⋆[lsmul ℝ ℝ, volume] g with hh
  refine ⟨h, ?_, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hgcont.locallyIntegrable
  · exact φ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hgc
  -- pointwise closeness
  have hclose : ∀ x, dist (h x) (g x) ≤ η := by
    intro x
    refine φ.dist_normed_convolution_le hgcont.aestronglyMeasurable fun y hy => ?_
    refine (hunif ?_).le
    have : dist y x < r := hy
    exact this.trans_le (min_le_left _ _)
  -- vanishing off `S`
  have hzero : ∀ x ∉ S, h x = 0 ∧ g x = 0 := by
    intro x hx
    have hgx : g x = 0 := by
      by_contra hne
      exact hx (self_subset_cthickening _ (subset_tsupport _ hne))
    refine ⟨?_, hgx⟩
    by_contra hne
    have hsupp := support_convolution_subset (lsmul ℝ ℝ) (μ := volume) (f := φ.normed volume)
      (g := g) hne
    obtain ⟨a, ha, b, hb, rfl⟩ := hsupp
    rw [φ.support_normed_eq, mem_ball_zero_iff] at ha
    refine hx (mem_cthickening_of_dist_le _ b 1 _ (subset_tsupport _ hb) ?_)
    rw [dist_eq_norm, add_sub_cancel_right]
    exact (ha.trans_le (min_le_right _ _)).le
  have hgh : eLpNorm (g - h) p volume ≤ ENNReal.ofReal (δ / 2) := by
    calc eLpNorm (g - h) p volume
        ≤ eLpNorm (S.indicator fun _ => η) p volume := by
          refine eLpNorm_mono fun x => ?_
          by_cases hx : x ∈ S
          · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos hη0, Pi.sub_apply,
              ← dist_eq_norm, dist_comm]
            exact hclose x
          · obtain ⟨h1, h2⟩ := hzero x hx
            rw [indicator_of_notMem hx, Pi.sub_apply, h1, h2, sub_zero, norm_zero, norm_zero]
      _ = ENNReal.ofReal η * X := by
          rw [eLpNorm_indicator_const hSm (by positivity) hp, ← ofReal_norm_eq_enorm,
            Real.norm_eq_abs, abs_of_pos hη0]
      _ ≤ ENNReal.ofReal (δ / 2) := by
          rw [← ENNReal.ofReal_toReal hXfin, ← ENNReal.ofReal_mul hη0.le]
          exact ENNReal.ofReal_le_ofReal hηc
  have hgm : AEStronglyMeasurable (g - h) volume :=
    hgcont.aestronglyMeasurable.sub (by
      exact (φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
        (n := 0) φ.contDiff_normed hgcont.locallyIntegrable).continuous.aestronglyMeasurable)
  calc eLpNorm (f - h) p volume = eLpNorm ((f - g) + (g - h)) p volume := by
        congr 1; abel
    _ ≤ eLpNorm (f - g) p volume + eLpNorm (g - h) p volume :=
        eLpNorm_add_le (hf.1.sub hgcont.aestronglyMeasurable) hgm hp1
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hfg hgh
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric ContinuousLinearMap
open scoped ENNReal Convolution

theorem solution {d : ℕ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hp : p ≠ ∞) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : MemLp f p volume) (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ h : EuclideanSpace ℝ (Fin d) → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ HasCompactSupport h ∧
      eLpNorm (f - h) p volume ≤ ENNReal.ofReal δ :=
  DbarRegularity.exists_contDiff_hasCompactSupport_eLpNorm_sub_le hp1 hp f hf δ hδ
