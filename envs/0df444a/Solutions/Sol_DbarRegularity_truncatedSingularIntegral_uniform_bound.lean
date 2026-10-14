-- Prove2me | solution 1 for DbarRegularity.truncatedSingularIntegral_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T18:13:05.451677+00:00
-- url     : https://prove2.me/submissions/86315223-bfe9-43e8-90ce-eecca9009988

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Theorems.Thm_DbarRegularity_eLpNorm_doubleTruncation_le
import Theorems.Thm_DbarRegularity_setIntegral_mul_eq_integral_indicator
import Theorems.Thm_DbarRegularity_memLp_indicator_le_norm
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Data.Real.ConjExponents



namespace DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

/-- Uniform `L^p` bound for the truncated singular integrals of a kernel satisfying Stein's
conditions (18)–(19), on all of `L^p`, `1 < p < ∞`, `d ≥ 1`. -/
theorem truncatedSingularIntegral_uniform_bound_aux {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨A, hA⟩ := eLpNorm_doubleTruncation_le hd K B hKm hK1 hK2 hK3 p hp
  refine ⟨A, fun ε hε f hf => ?_⟩
  have hpq : p.HolderConjugate p.conjExponent := Real.HolderConjugate.conjExponent hp
  haveI : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal p.conjExponent) 1 := by
    simpa using hpq.ennrealOfReal
  set Kε : EuclideanSpace ℝ (Fin d) → ℂ := {x | ε ≤ ‖x‖}.indicator K with hKε
  have hKεq : MemLp Kε (ENNReal.ofReal p.conjExponent) volume :=
    memLp_indicator_le_norm hd K hKm B hK1 ε hε _ hpq.symm.lt
  have hKεm : AEStronglyMeasurable Kε volume :=
    hKm.indicator (measurableSet_le measurable_const measurable_norm)
  simp_rw [setIntegral_mul_eq_integral_indicator K f ε]
  -- approximants
  set Kn : ℕ → EuclideanSpace ℝ (Fin d) → ℂ := fun n => {x | ‖x‖ < (n : ℝ) + 1}.indicator Kε
  set fn : ℕ → EuclideanSpace ℝ (Fin d) → ℂ := fun n => (ball (0 : EuclideanSpace ℝ (Fin d))
    ((n : ℝ) + 1)).indicator f
  set Fn : ℕ → EuclideanSpace ℝ (Fin d) → ℂ := fun n x => ∫ y, Kn n (x - y) * fn n y
  have hfn1 : ∀ n, Integrable (fn n) volume := by
    intro n
    rw [integrable_indicator_iff measurableSet_ball]
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d))
        ((n : ℝ) + 1))) := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    exact (hf.restrict _).integrable (by rw [ENNReal.one_le_ofReal]; exact hp.le)
  have hfnp : ∀ n, MemLp (fn n) (ENNReal.ofReal p) volume := fun n =>
    hf.indicator measurableSet_ball
  have hFn : ∀ n, eLpNorm (Fn n) (ENNReal.ofReal p) volume ≤
      A * eLpNorm f (ENNReal.ofReal p) volume := by
    intro n
    refine (hA ε ((n : ℝ) + 1) hε (by positivity) (fn n) (hfn1 n) (hfnp n)).trans ?_
    exact mul_le_mul' le_rfl (eLpNorm_indicator_le _)
  have hFnm : ∀ n, AEStronglyMeasurable (Fn n) volume := fun n =>
    aestronglyMeasurable_integral_mul_sub (Kn n) (fn n)
      (hKεm.indicator (measurableSet_lt measurable_norm measurable_const)) (hfn1 n).1
  -- pointwise convergence
  have hlim : ∀ x, Tendsto (fun n => Fn n x) atTop (𝓝 (∫ y, Kε (x - y) * f y)) := by
    intro x
    have hKx : MemLp (fun y => Kε (x - y)) (ENNReal.ofReal p.conjExponent) volume :=
      hKεq.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)
    have hdom : Integrable (fun y => ‖Kε (x - y)‖ * ‖f y‖) volume := by
      have := hKx.integrable_mul hf
      simpa [norm_mul] using this.norm
    refine tendsto_integral_of_dominated_convergence (fun y => ‖Kε (x - y)‖ * ‖f y‖) ?_ hdom ?_ ?_
    · intro n
      have h1 : AEStronglyMeasurable (Kn n) volume :=
        hKεm.indicator (measurableSet_lt measurable_norm measurable_const)
      exact (h1.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).mul
        (hfn1 n).1
    · intro n
      refine Eventually.of_forall fun y => ?_
      rw [norm_mul]
      exact mul_le_mul (norm_indicator_le_norm_self _ _) (norm_indicator_le_norm_self _ _)
        (norm_nonneg _) (norm_nonneg _)
    · refine Eventually.of_forall fun y => ?_
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (max ‖x - y‖ ‖y‖)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hn' : max ‖x - y‖ ‖y‖ < (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [max_lt_iff] at hn'
      simp only [Kn, fn]
      rw [indicator_of_mem (show x - y ∈ {x : EuclideanSpace ℝ (Fin d) | ‖x‖ < (n : ℝ) + 1}
        from hn'.1), indicator_of_mem (by rw [mem_ball_zero_iff]; exact hn'.2)]
  calc eLpNorm (fun x => ∫ y, Kε (x - y) * f y) (ENNReal.ofReal p) volume
      ≤ atTop.liminf fun n => eLpNorm (Fn n) (ENNReal.ofReal p) volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm hFnm _ (Eventually.of_forall hlim)
    _ ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
        liminf_le_of_frequently_le' (Frequently.of_forall hFn)

end DbarRegularity

open DbarRegularity

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem solution {d : ℕ} (hd : 0 < d)
    (K : EuclideanSpace ℝ (Fin d) → ℂ) (B : ℝ)
    (hKm : AEStronglyMeasurable K volume)
    (hK1 : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (hK2 : ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B)
    (hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y) (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
  DbarRegularity.truncatedSingularIntegral_uniform_bound_aux hd K B hKm hK1 hK2 hK3 p hp
