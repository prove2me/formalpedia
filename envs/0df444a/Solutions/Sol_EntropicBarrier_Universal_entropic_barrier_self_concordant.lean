-- Prove2me | solution 1 for EntropicBarrier.Universal.entropic_barrier_self_concordant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T13:52:06.007588+00:00
-- url     : https://prove2.me/submissions/2140f63c-4b05-4713-944e-b529eb6d61c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily
import Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_isBarrier
import Theorems.Thm_EntropicBarrier_Universal_entropicBarrier_selfConcordant
import Theorems.Thm_EntropicBarrier_Universal_nuBound_iff_covariance
import Theorems.Thm_EntropicBarrier_Universal_eq7_variance_bound

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

/-- Glue (proved inline): the covariance form along `θ` equals `‖θ‖²` times the variance of the
unit projection `⟪θ/‖θ‖, X⟫` under `p_θ`. -/
theorem covForm_self_eq_sq_mul_variance_0ac54f14 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (θ : EuclideanSpace ℝ (Fin n)) (hθ : θ ≠ 0) :
    covForm K θ θ θ =
      ‖θ‖ ^ 2 * ProbabilityTheory.variance (fun x => ⟪‖θ‖⁻¹ • θ, x⟫) (expFamily K θ) := by
  obtain ⟨hKc, -, -⟩ := hK
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  set L := logPartition K θ
  set g : EuclideanSpace ℝ (Fin n) → ENNReal := fun x => ENNReal.ofReal (Real.exp (⟪θ, x⟫ - L))
  have hgm : Measurable g := by
    apply ENNReal.measurable_ofReal.comp
    exact Real.measurable_exp.comp ((measurable_const.inner measurable_id).sub measurable_const)
  have hbound : ∀ x ∈ K, g x ≤ ENNReal.ofReal (Real.exp (‖θ‖ * R - L)) := by
    intro x hx
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have h1 : ⟪θ, x⟫ ≤ ‖θ‖ * ‖x‖ := real_inner_le_norm θ x
    have h2 : ‖θ‖ * ‖x‖ ≤ ‖θ‖ * R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg θ)
    linarith
  have hfin : IsFiniteMeasure (expFamily K θ) := by
    refine ⟨?_⟩
    unfold expFamily
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ x in K, g x ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp (‖θ‖ * R - L)) :=
          setLIntegral_mono measurable_const hbound
      _ = ENNReal.ofReal (Real.exp (‖θ‖ * R - L)) * volume K := by
          rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKc.measure_lt_top
  have hae : ∀ᵐ x ∂(expFamily K θ), x ∈ K := by
    unfold expFamily
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hKm)
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) (expFamily K θ) :=
    Integrable.of_bound aestronglyMeasurable_id R (hae.mono fun x hx => hR x hx)
  set u : EuclideanSpace ℝ (Fin n) := ‖θ‖⁻¹ • θ
  have hθn : ‖θ‖ ≠ 0 := norm_ne_zero_iff.mpr hθ
  have hθu : θ = ‖θ‖ • u := by
    simp only [u, smul_smul, mul_inv_cancel₀ hθn, one_smul]
  have key : ∀ y : EuclideanSpace ℝ (Fin n), ⟪y, θ⟫ = ‖θ‖ * ⟪u, y⟫ := fun y => by
    rw [real_inner_comm, ← real_inner_smul_left, ← hθu]
  have hmean : (∫ x, ⟪u, x⟫ ∂(expFamily K θ)) = ⟪u, meanMap K θ⟫ := by
    unfold meanMap
    exact integral_inner hint u
  have hXm : AEMeasurable (fun x : EuclideanSpace ℝ (Fin n) => ⟪u, x⟫) (expFamily K θ) :=
    (continuous_const.inner continuous_id).measurable.aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hXm]
  simp only [hmean]
  rw [← integral_const_mul]
  unfold covForm
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [inner_sub_left, key x, key (meanMap K θ)]
  ring

end EntropicBarrier.Universal

theorem solution {n : ℕ} (hn : 80 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : EntropicBarrier.Universal.IsConvexBody K) :
    EntropicBarrier.Universal.IsNuSelfConcordantBarrier K (EntropicBarrier.Universal.entropicBarrier K)
      ((1 + 100 * Real.sqrt (Real.log n / n)) * n) := by
  have hν : 0 ≤ (1 + 100 * Real.sqrt (Real.log n / n)) * (n : ℝ) := by positivity
  refine ⟨EntropicBarrier.Universal.entropicBarrier_isBarrier K hK,
    EntropicBarrier.Universal.entropicBarrier_selfConcordant K hK,
    (EntropicBarrier.Universal.nuBound_iff_covariance K hK _ hν).2 fun θ => ?_⟩
  by_cases hθ : θ = 0
  · subst hθ
    have h0 : EntropicBarrier.Universal.covForm K 0 0 0 = 0 := by
      simp [EntropicBarrier.Universal.covForm]
    rw [h0]
    exact hν
  · rw [EntropicBarrier.Universal.covForm_self_eq_sq_mul_variance_0ac54f14 K hK θ hθ]
    have hv := EntropicBarrier.Universal.eq7_variance_bound hn K hK θ hθ
    have hpos : 0 < ‖θ‖ ^ 2 := by positivity
    calc ‖θ‖ ^ 2 * ProbabilityTheory.variance (fun x => ⟪‖θ‖⁻¹ • θ, x⟫)
            (EntropicBarrier.Universal.expFamily K θ)
        ≤ ‖θ‖ ^ 2 * ((n : ℝ) / ‖θ‖ ^ 2 * (1 + 100 * Real.sqrt (Real.log n / n))) :=
          mul_le_mul_of_nonneg_left hv hpos.le
      _ = (1 + 100 * Real.sqrt (Real.log n / n)) * n := by
          field_simp
