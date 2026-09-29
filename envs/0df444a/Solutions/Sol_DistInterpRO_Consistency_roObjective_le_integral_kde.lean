-- Prove2me | solution 1 for DistInterpRO.Consistency.roObjective_le_integral_kde
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:24:07.754671+00:00
-- url     : https://prove2.me/submissions/5c25f3e6-03c3-46e3-989a-4742c3d6ca77

import Mathlib
import Definitions.Def_DistInterpRO_Consistency_Model

open MeasureTheory Filter Topology ProbabilityTheory

namespace DistInterpRO.Consistency

theorem aux_rokde_kernel_eq {m : ℕ} {ε : ℝ} (hε : 0 < ε) (g : (Fin m → ℝ) → ℝ)
    (y x : Fin m → ℝ) :
    g x * kernel (ε⁻¹ • (x - y)) =
      (Metric.closedBall y ε).indicator (fun z => g z * (1 / (2 : ℝ) ^ m)) x := by
  unfold kernel
  have hiff : ‖ε⁻¹ • (x - y)‖ ≤ 1 ↔ x ∈ Metric.closedBall y ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, Metric.mem_closedBall,
      dist_eq_norm, inv_mul_le_iff₀ hε, mul_one]
  by_cases h : x ∈ Metric.closedBall y ε
  · rw [if_pos (hiff.mpr h), Set.indicator_of_mem h]
  · rw [if_neg (fun h' => h (hiff.mp h')), Set.indicator_of_notMem h, mul_zero]

theorem aux_rokde_intOn {m : ℕ} {ε : ℝ} (hε : 0 < ε) (g : (Fin m → ℝ) → ℝ)
    (hg : Measurable g) (C : ℝ) (hgC : ∀ x, |g x| ≤ C) (y : Fin m → ℝ) :
    IntegrableOn g (Metric.closedBall y ε) volume := by
  apply Measure.integrableOn_of_bounded (M := C)
  · rw [Real.volume_pi_closedBall y hε.le]
    exact ENNReal.ofReal_ne_top
  · exact hg.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hgC x)

end DistInterpRO.Consistency

open DistInterpRO.Consistency

open MeasureTheory Filter Topology ProbabilityTheory

theorem solution {V : Type*} {m n : ℕ} (f : V → (Fin m → ℝ) → ℝ)
    (hfm : ∀ v, Measurable (f v)) (C : ℝ) (hfC : ∀ v x, |f v x| ≤ C)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (xs : Fin n → Fin m → ℝ) (v : V) :
    roObjective f ε xs v ≤ ∫ x, f v x * kde ε xs x := by
  have hB : ∀ i, MeasurableSet (Metric.closedBall (xs i) ε) :=
    fun i => measurableSet_closedBall
  have hint : ∀ i, Integrable (fun x => f v x * kernel (ε⁻¹ • (x - xs i))) := by
    intro i
    simp_rw [aux_rokde_kernel_eq hε (f v) (xs i)]
    rw [integrable_indicator_iff (hB i)]
    exact (aux_rokde_intOn hε (f v) (hfm v) C (hfC v) (xs i)).mul_const _
  have heq : (fun x => f v x * kde ε xs x) =
      fun x => ((n : ℝ) * ε ^ m)⁻¹ * ∑ i : Fin n, f v x * kernel (ε⁻¹ • (x - xs i)) := by
    funext x
    unfold kde
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq, integral_const_mul, integral_finsetSum _ (fun i _ => hint i)]
  unfold roObjective
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- the i-th term
  set c := ⨅ δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε}, f v (xs i + δ.1) with hc
  have hbdd : BddBelow (Set.range fun δ : {δ : Fin m → ℝ // ‖δ‖ ≤ ε} => f v (xs i + δ.1)) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨δ, rfl⟩
    exact (abs_le.mp (hfC v _)).1
  have hle : ∀ x ∈ Metric.closedBall (xs i) ε, c ≤ f v x := by
    intro x hx
    have hx' : ‖x - xs i‖ ≤ ε := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx; exact hx
    have := ciInf_le hbdd ⟨x - xs i, hx'⟩
    simpa using this
  have hI := setIntegral_ge_of_const_le_real (hB i)
    (by rw [Real.volume_pi_closedBall (xs i) hε.le]; exact ENNReal.ofReal_ne_top) hle
    (aux_rokde_intOn hε (f v) (hfm v) C (hfC v) (xs i))
  have hvol : volume.real (Metric.closedBall (xs i) ε) = (2 * ε) ^ m := by
    rw [Measure.real, Real.volume_pi_closedBall (xs i) hε.le, Fintype.card_fin,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hvol] at hI
  have hint_i : ∫ x, f v x * kernel (ε⁻¹ • (x - xs i)) =
      (∫ x in Metric.closedBall (xs i) ε, f v x) * (1 / (2 : ℝ) ^ m) := by
    simp_rw [aux_rokde_kernel_eq hε (f v) (xs i)]
    rw [integral_indicator (hB i), integral_mul_const]
  rw [hint_i]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hεm : (0 : ℝ) < ε ^ m := by positivity
  rw [mul_pow] at hI
  have key : 1 / (n : ℝ) * c = ((n : ℝ) * ε ^ m)⁻¹ * (c * (2 ^ m * ε ^ m) * (1 / 2 ^ m)) := by
    field_simp
  rw [key]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_right hI (by positivity)
