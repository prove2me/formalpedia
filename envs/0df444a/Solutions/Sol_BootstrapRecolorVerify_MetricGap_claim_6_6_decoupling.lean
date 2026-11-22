-- Prove2me | solution 1 for BootstrapRecolorVerify.MetricGap.claim_6_6_decoupling
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T18:36:19.064548+00:00
-- url     : https://prove2.me/submissions/92c3dfe7-68ad-440d-b208-09750a34fc7e

import Mathlib

open MeasureTheory
open scoped ENNReal

/-- Claim 6.6 (metric decoupling). Take two independent copies `(X₁,Y₁)`, `(X₂,Y₂)` of the
joint law, i.e. the measure `μ.prod μ`. Then `X₁, Y₂` are independent with the right marginals,
and averaging the triangle inequalities through `Y₁` and through `X₂` gives the bound. -/
theorem solution {S : Type*} [PseudoMetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure (S × S)) [IsProbabilityMeasure μ]
    (hXY : AEMeasurable (fun p : S × S => edist p.1 p.2) μ)
    (hind : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.fst).prod (μ.map Prod.snd)))
    (hXX : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.fst).prod (μ.map Prod.fst)))
    (hYY : AEMeasurable (fun p : S × S => edist p.1 p.2)
      ((μ.map Prod.snd).prod (μ.map Prod.snd))) :
    (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.fst).prod (μ.map Prod.snd))) ≤
      (∫⁻ p : S × S, edist p.1 p.2 ∂μ) +
      (1 / 2 : ℝ≥0∞) *
        (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.fst).prod (μ.map Prod.fst))) +
      (1 / 2 : ℝ≥0∞) *
        (∫⁻ p : S × S, edist p.1 p.2 ∂((μ.map Prod.snd).prod (μ.map Prod.snd))) := by
  set d : S × S → ℝ≥0∞ := fun p => edist p.1 p.2 with hd
  set ν : Measure ((S × S) × (S × S)) := μ.prod μ with hν
  -- the coordinate maps out of two independent copies
  have m11 : Measurable (fun q : (S × S) × (S × S) => (q.1.1, q.2.2)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have m1 : Measurable (fun q : (S × S) × (S × S) => q.1) := measurable_fst
  have m2 : Measurable (fun q : (S × S) × (S × S) => q.2) := measurable_snd
  have mXX : Measurable (fun q : (S × S) × (S × S) => (q.1.1, q.2.1)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have mYY : Measurable (fun q : (S × S) × (S × S) => (q.1.2, q.2.2)) :=
    (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)
  have eind : ν.map (fun q => (q.1.1, q.2.2)) = (μ.map Prod.fst).prod (μ.map Prod.snd) := by
    rw [Measure.map_prod_map _ _ measurable_fst measurable_snd]; rfl
  have eXX : ν.map (fun q => (q.1.1, q.2.1)) = (μ.map Prod.fst).prod (μ.map Prod.fst) := by
    rw [Measure.map_prod_map _ _ measurable_fst measurable_fst]; rfl
  have eYY : ν.map (fun q => (q.1.2, q.2.2)) = (μ.map Prod.snd).prod (μ.map Prod.snd) := by
    rw [Measure.map_prod_map _ _ measurable_snd measurable_snd]; rfl
  have e1 : ν.map (fun q => q.1) = μ := by
    rw [hν, Measure.map_fst_prod]; simp
  have e2 : ν.map (fun q => q.2) = μ := by
    rw [hν, Measure.map_snd_prod]; simp
  have hind' := hind; have hXX' := hXX; have hYY' := hYY
  have hXY1 := hXY; have hXY2 := hXY
  rw [← eind] at hind'; rw [← eXX] at hXX'; rw [← eYY] at hYY'
  rw [← e1] at hXY1; rw [← e2] at hXY2
  have Lind := lintegral_map' hind' m11.aemeasurable
  have LXX := lintegral_map' hXX' mXX.aemeasurable
  have LYY := lintegral_map' hYY' mYY.aemeasurable
  have L1 := lintegral_map' hXY1 m1.aemeasurable
  have L2 := lintegral_map' hXY2 m2.aemeasurable
  rw [eind] at Lind; rw [eXX] at LXX; rw [eYY] at LYY; rw [e1] at L1; rw [e2] at L2
  have a1 := hXY1.comp_aemeasurable m1.aemeasurable
  have a2 := hXY2.comp_aemeasurable m2.aemeasurable
  have aXX := hXX'.comp_aemeasurable mXX.aemeasurable
  -- pointwise inequality: average of two triangle inequalities
  have pw : ∀ q : (S × S) × (S × S),
      2 * edist q.1.1 q.2.2 ≤
        (edist q.1.1 q.1.2 + edist q.2.1 q.2.2) + edist q.1.1 q.2.1 + edist q.1.2 q.2.2 := by
    intro q
    have h1 : edist q.1.1 q.2.2 ≤ edist q.1.1 q.1.2 + edist q.1.2 q.2.2 := edist_triangle _ _ _
    have h2 : edist q.1.1 q.2.2 ≤ edist q.1.1 q.2.1 + edist q.2.1 q.2.2 := edist_triangle _ _ _
    calc 2 * edist q.1.1 q.2.2 = edist q.1.1 q.2.2 + edist q.1.1 q.2.2 := two_mul _
      _ ≤ (edist q.1.1 q.1.2 + edist q.1.2 q.2.2) + (edist q.1.1 q.2.1 + edist q.2.1 q.2.2) :=
          add_le_add h1 h2
      _ = _ := by ring
  have key : 2 * (∫⁻ p, d p ∂((μ.map Prod.fst).prod (μ.map Prod.snd))) ≤
      (∫⁻ p, d p ∂μ + ∫⁻ p, d p ∂μ) + (∫⁻ p, d p ∂((μ.map Prod.fst).prod (μ.map Prod.fst)))
        + (∫⁻ p, d p ∂((μ.map Prod.snd).prod (μ.map Prod.snd))) := by
    rw [Lind, LXX, LYY]
    nth_rw 2 [L2]
    rw [L1, ← lintegral_const_mul' _ _ (by norm_num)]
    have s1 : ∫⁻ q, (d q.1 + d q.2) ∂ν = ∫⁻ q, d q.1 ∂ν + ∫⁻ q, d q.2 ∂ν :=
      lintegral_add_left' a1 _
    have s2 : ∫⁻ q, (d q.1 + d q.2 + d (q.1.1, q.2.1)) ∂ν =
        ∫⁻ q, (d q.1 + d q.2) ∂ν + ∫⁻ q, d (q.1.1, q.2.1) ∂ν :=
      lintegral_add_left' (a1.add a2) _
    have s3 : ∫⁻ q, (d q.1 + d q.2 + d (q.1.1, q.2.1) + d (q.1.2, q.2.2)) ∂ν =
        ∫⁻ q, (d q.1 + d q.2 + d (q.1.1, q.2.1)) ∂ν + ∫⁻ q, d (q.1.2, q.2.2) ∂ν :=
      lintegral_add_left' ((a1.add a2).add aXX) _
    rw [← s1, ← s2, ← s3]
    exact lintegral_mono fun q => pw q
  set A := ∫⁻ p, d p ∂((μ.map Prod.fst).prod (μ.map Prod.snd))
  set B := ∫⁻ p, d p ∂μ
  set C := ∫⁻ p, d p ∂((μ.map Prod.fst).prod (μ.map Prod.fst))
  set D := ∫⁻ p, d p ∂((μ.map Prod.snd).prod (μ.map Prod.snd))
  have h2 : (1 / 2 : ℝ≥0∞) * 2 = 1 := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  calc A = (1 / 2 : ℝ≥0∞) * (2 * A) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ (1 / 2 : ℝ≥0∞) * ((B + B) + C + D) := by gcongr
    _ = B + 1 / 2 * C + 1 / 2 * D := by
      rw [← two_mul, mul_add, mul_add, ← mul_assoc, h2, one_mul]
