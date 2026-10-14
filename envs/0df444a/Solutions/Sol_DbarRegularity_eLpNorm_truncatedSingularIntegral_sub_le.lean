-- Prove2me | solution 1 for DbarRegularity.eLpNorm_truncatedSingularIntegral_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:18:15.467816+00:00
-- url     : https://prove2.me/submissions/0f6a4e81-2a7a-4023-af5f-89862c0ad220

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_DbarRegularity_memLp_indicator_le_norm
import Theorems.Thm_DbarRegularity_integral_ball_norm_rpow_one_sub
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Data.Real.ConjExponents



namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal NNReal

/-- For a kernel with `|K(x)| ≤ B |x|^{-d}` and vanishing integrals over annuli, and a compactly
supported `C¹` function `f`, the truncated singular integrals satisfy
`‖T_ε f - T_η f‖_p ≤ C η` for `0 < ε ≤ η ≤ 1`, with `C` depending on `f` (and `K`, `p`). -/
theorem eLpNorm_truncatedSingularIntegral_sub_le_aux {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε η : ℝ, 0 < ε → ε ≤ η → η ≤ 1 →
      eLpNorm ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) -
          (fun x => ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * η) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hB : 0 ≤ B := by
    obtain ⟨x, hx⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin d))
    have := (norm_nonneg _).trans (hK1 x hx)
    exact (div_nonneg_iff.1 this).elim (fun h => h.1)
      (fun h => absurd h.2 (not_le.2 (by have := norm_pos_iff.2 hx; positivity)))
  obtain ⟨L, hL⟩ := hf.lipschitzWith_of_hasCompactSupport hfc one_ne_zero
  set S : Set (EuclideanSpace ℝ (Fin d)) := cthickening 1 (tsupport f) with hS
  have hScpt : IsCompact S := hfc.isCompact.cthickening
  have hSm : MeasurableSet S := isClosed_cthickening.measurableSet
  have hSfin : volume S ≠ ∞ := hScpt.measure_lt_top.ne
  set X : ℝ≥0∞ := volume S ^ (1 / (ENNReal.ofReal p).toReal) with hX
  have hXfin : X ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hSfin
  set Vr : ℝ := volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
  have hVr : 0 ≤ Vr := ENNReal.toReal_nonneg
  set M : ℝ := L * B * (d * Vr) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M * X.toReal, fun ε η hε hεη hη1 => ?_⟩
  have hη : 0 < η := hε.trans_le hεη
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  haveI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) 1 := by
    simpa using hpq.ennrealOfReal
  have hfp : MemLp f (ENNReal.ofReal p) volume :=
    hf.continuous.memLp_of_hasCompactSupport hfc
  have hmeas_le : ∀ r : ℝ, MeasurableSet {y : EuclideanSpace ℝ (Fin d) | r ≤ ‖y‖} := fun r =>
    measurableSet_le measurable_const measurable_norm
  -- integrability of the integrands
  have hInt : ∀ x (r : ℝ), 0 < r →
      IntegrableOn (fun y => f (x - y) * K y) {y | r ≤ ‖y‖} volume := by
    intro x r hr
    have hKr : MemLp ({y | r ≤ ‖y‖}.indicator K) (ENNReal.ofReal p.conjExponent) volume :=
      memLp_indicator_le_norm hd K hKm B hK1 r hr _ hpq.symm.lt
    have hfx : MemLp (fun y => f (x - y)) (ENNReal.ofReal p) volume :=
      hfp.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    have := hfx.integrable_mul hKr
    rw [← integrable_indicator_iff (hmeas_le r)]
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply, indicator]
    split_ifs <;> simp
  set A : Set (EuclideanSpace ℝ (Fin d)) := {y | ε ≤ ‖y‖} \ {y | η ≤ ‖y‖} with hA
  have hAm : MeasurableSet A := (hmeas_le ε).diff (hmeas_le η)
  have hAball : A ⊆ ball 0 η := by
    intro y hy
    simp only [hA, mem_diff, mem_setOf_eq, not_le] at hy
    rw [mem_ball_zero_iff]; exact hy.2
  -- cancellation on `A`
  have hKA : ∫ y in A, K y = 0 := by
    have hae : A =ᵐ[volume] {y : EuclideanSpace ℝ (Fin d) | ε < ‖y‖ ∧ ‖y‖ < η} := by
      refine (ae_eq_set).2 ⟨?_, ?_⟩
      · refine measure_mono_null (t := sphere (0 : EuclideanSpace ℝ (Fin d)) ε) ?_
          (Measure.addHaar_sphere _ _ _)
        intro y hy
        simp only [hA, mem_diff, mem_setOf_eq, not_le, not_and, not_lt] at hy
        simp only [mem_sphere_zero_iff_norm]
        by_contra hne
        have h' : ε < ‖y‖ := lt_of_le_of_ne hy.1.1 (Ne.symm hne)
        exact absurd hy.1.2 (not_lt.2 (hy.2 h'))
      · have : {y : EuclideanSpace ℝ (Fin d) | ε < ‖y‖ ∧ ‖y‖ < η} \ A = ∅ := by
          ext y
          simp only [hA, mem_diff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
          rintro ⟨⟨h1, h2⟩, h3⟩
          exact h3 ⟨h1.le, h2⟩
        rw [this, measure_empty]
    rw [setIntegral_congr_set hae]
    rcases hεη.lt_or_eq with hlt | heq
    · exact hK3 ε η hε hlt
    · have : {y : EuclideanSpace ℝ (Fin d) | ε < ‖y‖ ∧ ‖y‖ < η} = ∅ := by
        ext y; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro h; rw [← heq]; exact h.le
      rw [this, Measure.restrict_empty, integral_zero_measure]
  have hKAi : IntegrableOn K A volume := by
    have hKε : MemLp ({y | ε ≤ ‖y‖}.indicator K) 2 volume := by
      simpa using memLp_indicator_le_norm hd K hKm B hK1 ε hε 2 one_lt_two
    haveI : IsFiniteMeasure (volume.restrict A) :=
      isFiniteMeasure_restrict.2 ((measure_mono hAball).trans_lt measure_ball_lt_top).ne
    have h1 : IntegrableOn ({y | ε ≤ ‖y‖}.indicator K) A volume :=
      (hKε.restrict A).integrable one_le_two
    refine h1.congr_fun (fun y hy => ?_) hAm
    exact indicator_of_mem hy.1 _
  -- radial integral
  obtain ⟨hgi, hgv⟩ := integral_ball_norm_rpow_one_sub hd η hη
  -- pointwise estimate
  have hpt : ∀ x, ‖(fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) x -
      (fun x => ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y) x‖ ≤ S.indicator (fun _ => M * η) x := by
    intro x
    show ‖(∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) - ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y‖ ≤ _
    have hts : {y : EuclideanSpace ℝ (Fin d) | η ≤ ‖y‖} ⊆ {y | ε ≤ ‖y‖} :=
      fun y hy => hεη.trans hy
    have hsub : (∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) - ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y
        = ∫ y in A, f (x - y) * K y :=
      (integral_diff (hmeas_le η) (hInt x ε hε) hts).symm
    rw [hsub]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      have h2 : ∫ y in A, f (x - y) * K y = ∫ y in A, (f (x - y) - f x) * K y := by
        simp_rw [sub_mul]
        rw [integral_sub ((hInt x ε hε).mono_set diff_subset) (hKAi.const_mul (f x)),
          integral_const_mul, hKA, mul_zero, sub_zero]
      rw [h2]
      have hbd : ∀ᵐ y ∂(volume.restrict A), ‖(f (x - y) - f x) * K y‖ ≤
          (L * B) * ‖y‖ ^ (1 - d : ℝ) := by
        refine ae_restrict_of_forall_mem hAm fun y hy => ?_
        have hy0 : 0 < ‖y‖ := hε.trans_le hy.1
        have hyne : y ≠ 0 := norm_pos_iff.1 hy0
        rw [norm_mul]
        have hlip : ‖f (x - y) - f x‖ ≤ L * ‖y‖ := by
          have := hL.dist_le_mul (x - y) x
          rwa [dist_eq_norm, dist_eq_norm, sub_sub_cancel_left, norm_neg] at this
        calc ‖f (x - y) - f x‖ * ‖K y‖ ≤ (L * ‖y‖) * (B / ‖y‖ ^ d) :=
              mul_le_mul hlip (hK1 y hyne) (norm_nonneg _) (by positivity)
          _ = (L * B) * ‖y‖ ^ (1 - d : ℝ) := by
              rw [Real.rpow_sub hy0, Real.rpow_one, Real.rpow_natCast]; ring
      have hgA : IntegrableOn (fun y : EuclideanSpace ℝ (Fin d) => (L * B) * ‖y‖ ^ (1 - d : ℝ))
          A volume := IntegrableOn.mono_set (t := ball 0 η) (hgi.const_mul (L * B)) hAball
      calc ‖∫ y in A, (f (x - y) - f x) * K y‖
          ≤ ∫ y in A, (L * B) * ‖y‖ ^ (1 - d : ℝ) := norm_integral_le_of_norm_le hgA hbd
        _ ≤ ∫ y in ball (0 : EuclideanSpace ℝ (Fin d)) η, (L * B) * ‖y‖ ^ (1 - d : ℝ) := by
            refine setIntegral_mono_set (hgi.const_mul _) ?_ (Filter.Eventually.of_forall hAball)
            exact Filter.Eventually.of_forall fun y => by positivity
        _ = M * η := by rw [integral_const_mul, hgv, hM]; ring
    · rw [indicator_of_notMem hxS]
      have h0 : ∫ y in A, f (x - y) * K y = 0 := by
        refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
        have hy1 : ‖y‖ < 1 := (mem_ball_zero_iff.1 (hAball hy)).trans_le hη1
        have : f (x - y) = 0 := by
          by_contra hne
          refine hxS (mem_cthickening_of_dist_le x (x - y) 1 _ (subset_tsupport _ hne) ?_)
          rw [dist_eq_norm, sub_sub_cancel]; exact hy1.le
        rw [this, zero_mul]
      rw [h0, norm_zero]
  calc _ ≤ eLpNorm (S.indicator fun _ => M * η) (ENNReal.ofReal p) volume :=
        eLpNorm_mono fun x => (hpt x).trans (le_of_eq (by
          by_cases hx : x ∈ S
          · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          · rw [indicator_of_notMem hx, norm_zero]))
    _ = ENNReal.ofReal (M * η) * X := by
        rw [eLpNorm_indicator_const hSm (by simp; linarith) ENNReal.ofReal_ne_top,
          ← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ = ENNReal.ofReal (M * X.toReal * η) := by
        rw [← ENNReal.ofReal_toReal hXfin, ← ENNReal.ofReal_mul (by positivity),
          ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
        ring_nf

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) :
    ∃ C : ℝ, ∀ ε η : ℝ, 0 < ε → ε ≤ η → η ≤ 1 →
      eLpNorm ((fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) -
          (fun x => ∫ y in {y | η ≤ ‖y‖}, f (x - y) * K y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * η) :=
  DbarRegularity.eLpNorm_truncatedSingularIntegral_sub_le_aux hd K B hKm hK1 hK3 p hp f hf hfc
