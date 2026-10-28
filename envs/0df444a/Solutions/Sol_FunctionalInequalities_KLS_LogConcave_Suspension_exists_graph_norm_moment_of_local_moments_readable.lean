-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:51.856202+00:00
-- url     : https://prove2.me/submissions/817a54b2-79a9-481c-aec2-3a3fae6162e2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Cumulant

noncomputable section
open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace
/-- **Exponential moment of the graph law** `x ↦ (f x, x)` from exponential moments of `|f|` and
`‖x‖` (Cauchy–Schwarz in `L²`, at rate `min a s / 2`). -/
theorem solution {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {a s : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hfa : Integrable (fun x => Real.exp (a * |f x|)) μ)
    (hxs : Integrable (fun x => Real.exp (s * ‖x‖)) μ) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        (μ.map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) := by
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Option (Fin n)) :=
    fun x => WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j
  have hgm : Measurable g := by
    dsimp [g]
    apply (WithLp.measurable_toLp 2 _).comp
    rw [measurable_pi_iff]
    intro o
    cases o with
    | none => exact hf
    | some j => exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have hsq (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_option]
    change (f x) ^ 2 + ∑ j : Fin n, (x j) ^ 2 = |f x| ^ 2 + ‖x‖ ^ 2
    rw [sq_abs, ← EuclideanSpace.real_norm_sq_eq]
  have hbound (x : EuclideanSpace ℝ (Fin n)) : ‖g x‖ ≤ |f x| + ‖x‖ := by
    nlinarith [hsq x, norm_nonneg (g x), abs_nonneg (f x), norm_nonneg x,
      mul_nonneg (abs_nonneg (f x)) (norm_nonneg x)]
  let t : ℝ := min a s / 2
  have ht : 0 < t := div_pos (lt_min ha hs) (by norm_num)
  have h2a : 2 * t ≤ a := by dsimp [t]; linarith [min_le_left a s]
  have h2s : 2 * t ≤ s := by dsimp [t]; linarith [min_le_right a s]
  let U : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * |f x|)
  let V : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (t * ‖x‖)
  have hmU : AEStronglyMeasurable U μ :=
    (by fun_prop : Measurable U).aestronglyMeasurable
  have hmV : AEStronglyMeasurable V μ :=
    (by fun_prop : Continuous V).aestronglyMeasurable
  have hU2 : Integrable (fun x => U x ^ 2) μ := by
    refine hfa.mono' ((by fun_prop : Measurable (fun x => U x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [U]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * |f x| + t * |f x| = (2 * t) * |f x| := by ring
      _ ≤ a * |f x| := mul_le_mul_of_nonneg_right h2a (abs_nonneg _)
  have hV2 : Integrable (fun x => V x ^ 2) μ := by
    refine hxs.mono' ((by fun_prop : Continuous (fun x => V x ^ 2)).aestronglyMeasurable) ?_
    filter_upwards [] with x
    dsimp [V]
    rw [abs_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      t * ‖x‖ + t * ‖x‖ = (2 * t) * ‖x‖ := by ring
      _ ≤ s * ‖x‖ := mul_le_mul_of_nonneg_right h2s (norm_nonneg _)
  have hULp : MemLp U 2 μ := (memLp_two_iff_integrable_sq hmU).mpr hU2
  have hVLp : MemLp V 2 μ := (memLp_two_iff_integrable_sq hmV).mpr hV2
  have hUV : Integrable (fun x => U x * V x) μ := hULp.integrable_mul hVLp
  have hgint : Integrable (fun x => Real.exp (t * ‖g x‖)) μ := by
    refine hUV.mono'
      ((by fun_prop : Measurable (fun x => Real.exp (t * ‖g x‖))).aestronglyMeasurable) ?_
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    dsimp [U, V]
    calc
      Real.exp (t * ‖g x‖) ≤ Real.exp (t * (|f x| + ‖x‖)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbound x) ht.le)
      _ = Real.exp (t * |f x|) * Real.exp (t * ‖x‖) := by rw [mul_add, Real.exp_add]
  refine ⟨t, ht, ?_⟩
  exact (integrable_map_measure
    ((by fun_prop : Continuous
      (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))).aestronglyMeasurable)
    hgm.aemeasurable).mpr hgint
