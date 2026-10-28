-- Prove2me | solution 1 for EntropicBarrier.Universal.entropicBarrier_isBarrier
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T11:56:51.122783+00:00
-- url     : https://prove2.me/submissions/fb7f05a3-80c9-4751-909a-599367f4fa0e

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier

open scoped RealInnerProductSpace
open MeasureTheory

set_option autoImplicit false

namespace EB5ef

open Filter Topology Metric

/-- Upper bound on the family defining the entropic barrier at an interior point. -/
lemma family_le {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKc : IsCompact K) {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : ball x r ⊆ K) (θ : EuclideanSpace ℝ (Fin n)) :
    ⟪θ, x⟫ - EntropicBarrier.Universal.logPartition K θ ≤
      - Real.log ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))).toReal) := by
  set V := (volume (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 2))).toReal with hV
  have hVpos : 0 < V := by
    rw [hV]
    exact ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
      measure_ball_lt_top.ne
  set c : EuclideanSpace ℝ (Fin n) := x + (r / 2) • ((‖θ‖)⁻¹ • θ) with hc
  set B := ball c (r / 2) with hB
  have hBK : B ⊆ K := by
    intro y hy
    apply hball
    rw [mem_ball] at hy ⊢
    have h1 : dist c x ≤ r / 2 := by
      rw [hc, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul]
      rcases eq_or_ne θ 0 with h0 | h0
      · simp [h0]; linarith
      · rw [norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
        simp [abs_of_pos hr]
    linarith [dist_triangle y c x]
  have hvolB : (volume B).toReal = V := by
    rw [hB, hV, Measure.addHaar_ball_center]
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, y⟫ := by
    fun_prop
  have hint : IntegrableOn (fun y => Real.exp ⟪θ, y⟫) K volume :=
    hcont.continuousOn.integrableOn_compact hKc
  have hlow : ∀ y ∈ B, Real.exp ⟪θ, x⟫ ≤ Real.exp ⟪θ, y⟫ := by
    intro y hy
    apply Real.exp_le_exp.2
    rw [mem_ball, dist_eq_norm] at hy
    have hy' : y = c + (y - c) := by abel
    rw [hy', inner_add_right, hc, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    have hcs : -(‖θ‖ * ‖y - c‖) ≤ ⟪θ, y - c⟫ := by
      have := abs_real_inner_le_norm θ (y - c)
      linarith [neg_abs_le ⟪θ, y - c⟫]
    have hθ : (‖θ‖)⁻¹ * ‖θ‖ ^ 2 = ‖θ‖ := by
      rcases eq_or_ne ‖θ‖ 0 with h0 | h0
      · simp [h0]
      · field_simp
    rw [hθ]
    nlinarith [norm_nonneg θ]
  have hBint : V * Real.exp ⟪θ, x⟫ ≤ ∫ y in K, Real.exp ⟪θ, y⟫ := by
    calc V * Real.exp ⟪θ, x⟫ = ∫ _ in B, Real.exp ⟪θ, x⟫ := by
          rw [setIntegral_const, smul_eq_mul, ← hvolB, Measure.real]
      _ ≤ ∫ y in B, Real.exp ⟪θ, y⟫ := by
          apply setIntegral_mono_on
          · exact integrableOn_const (measure_ball_lt_top).ne
          · exact hint.mono_set hBK
          · exact isOpen_ball.measurableSet
          · exact hlow
      _ ≤ ∫ y in K, Real.exp ⟪θ, y⟫ := by
          apply setIntegral_mono_set hint
          · exact Eventually.of_forall (fun y => (Real.exp_pos _).le)
          · exact Eventually.of_forall hBK
  have hpos : 0 < V * Real.exp ⟪θ, x⟫ := mul_pos hVpos (Real.exp_pos _)
  unfold EntropicBarrier.Universal.logPartition
  have := Real.log_le_log hpos hBint
  rw [Real.log_mul hVpos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  linarith

/-- Supporting hyperplane at a frontier point. -/
lemma support {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : EntropicBarrier.Universal.IsConvexBody K) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ frontier K) :
    ∃ u : EuclideanSpace ℝ (Fin n), (∀ a ∈ interior K, ⟪u, a⟫ < ⟪u, x₀⟫) ∧
      (∀ y ∈ K, ⟪u, y⟫ ≤ ⟪u, x₀⟫) := by
  obtain ⟨hKc, hKcv, hKi⟩ := hK
  have hx₀i : x₀ ∉ interior K := hx₀.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hKcv.interior isOpen_interior hx₀i
  refine ⟨(InnerProductSpace.toDual ℝ _).symm f, ?_, ?_⟩
  · intro a ha
    simpa [InnerProductSpace.toDual_symm_apply] using hf a ha
  · intro y hy
    have hcl : closure (interior K) ⊆ {z | f z ≤ f x₀} :=
      closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
    rw [hKcv.closure_interior_eq_closure_of_nonempty_interior hKi] at hcl
    have := hcl (subset_closure hy)
    simpa [InnerProductSpace.toDual_symm_apply] using this

/-- The normalised partition function along the outer normal tends to zero. -/
lemma J_tendsto {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : EntropicBarrier.Universal.IsConvexBody K) (u : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (hint : ∀ a ∈ interior K, ⟪u, a⟫ < c) (hle : ∀ y ∈ K, ⟪u, y⟫ ≤ c) :
    Tendsto (fun t : ℝ => ∫ y in K, Real.exp (t * (⟪u, y⟫ - c))) atTop (𝓝 0) := by
  obtain ⟨hKc, hKcv, hKi⟩ := hK
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  have h0 : (∫ _y in K, (0 : ℝ)) = 0 := by simp
  rw [← h0]
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
  · exact Eventually.of_forall (fun t => by
      apply Continuous.aestronglyMeasurable; fun_prop)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [ae_restrict_iff' hKc.isClosed.measurableSet]
    refine Eventually.of_forall (fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := hle y hy
    nlinarith
  · exact integrable_const _
  · have hfr : volume (frontier K) = 0 := hKcv.addHaar_frontier volume
    have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), y ∉ frontier K :=
      measure_eq_zero_iff_ae_notMem.1 hfr
    rw [ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae] with y hy hyK
    have hyi : y ∈ interior K := by
      by_contra h
      exact hy ⟨subset_closure hyK, h⟩
    have hneg : ⟪u, y⟫ - c < 0 := by linarith [hint y hyi]
    have : Tendsto (fun t : ℝ => t * (⟪u, y⟫ - c)) atTop atBot :=
      tendsto_id.atTop_mul_const_of_neg hneg
    exact Real.tendsto_exp_atBot.comp this

lemma J_pos {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : EntropicBarrier.Universal.IsConvexBody K) (u : EuclideanSpace ℝ (Fin n)) (c t : ℝ) :
    0 < ∫ y in K, Real.exp (t * (⟪u, y⟫ - c)) := by
  obtain ⟨hKc, hKcv, hKi⟩ := hK
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  have hne : volume K ≠ 0 := by
    intro h
    have := measure_mono_null interior_subset h
    exact (isOpen_interior.measure_pos volume hKi).ne' this
  have : NeZero (volume.restrict K) := ⟨by
    rw [Ne, Measure.restrict_eq_zero]; exact hne⟩
  apply integral_exp_pos
  exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact hKc

lemma logPartition_smul {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : EntropicBarrier.Universal.IsConvexBody K) (u : EuclideanSpace ℝ (Fin n)) (c t : ℝ) :
    EntropicBarrier.Universal.logPartition K (t • u) =
      t * c + Real.log (∫ y in K, Real.exp (t * (⟪u, y⟫ - c))) := by
  unfold EntropicBarrier.Universal.logPartition
  have : (fun y : EuclideanSpace ℝ (Fin n) => Real.exp ⟪t • u, y⟫) =
      fun y => Real.exp (t * c) * Real.exp (t * (⟪u, y⟫ - c)) := by
    funext y
    rw [← Real.exp_add, real_inner_smul_left]
    ring_nf
  rw [this, integral_const_mul, Real.log_mul (Real.exp_pos _).ne' (J_pos K hK u c t).ne',
    Real.log_exp]

end EB5ef

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) :
    IsBarrier K (entropicBarrier K) := by
  intro x₀ hx₀
  obtain ⟨u, hu1, hu2⟩ := EB5ef.support K hK hx₀
  set c := ⟪u, x₀⟫ with hc
  rw [Filter.tendsto_atTop]
  intro M
  have hJ := EB5ef.J_tendsto K hK u c hu1 hu2
  obtain ⟨t, ht⟩ := (hJ.eventually (gt_mem_nhds (Real.exp_pos (-(M + 1))))).exists
  have hcont : Filter.Tendsto (fun x : EuclideanSpace ℝ (Fin n) => t * (⟪u, x⟫ - c))
      (nhdsWithin x₀ (interior K)) (nhds (t * (⟪u, x₀⟫ - c))) := by
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    exact ((continuous_const.mul ((continuous_const.inner continuous_id).sub
      continuous_const))).tendsto x₀
  rw [← hc, sub_self, mul_zero] at hcont
  filter_upwards [self_mem_nhdsWithin, hcont.eventually (lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num))]
    with x hx hx1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  have hbdd : BddAbove (Set.range fun θ : EuclideanSpace ℝ (Fin n) =>
      ⟪θ, x⟫ - logPartition K θ) := by
    refine ⟨- Real.log ((MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n))
      (r / 2))).toReal), ?_⟩
    rintro _ ⟨θ, rfl⟩
    exact EB5ef.family_le K hK.1 hr (hball.trans interior_subset) θ
  have hle : ⟪t • u, x⟫ - logPartition K (t • u) ≤ entropicBarrier K x :=
    le_ciSup hbdd (t • u)
  rw [EB5ef.logPartition_smul K hK u c t, real_inner_smul_left] at hle
  have hlog : Real.log (∫ y in K, Real.exp (t * (⟪u, y⟫ - c))) < -(M + 1) := by
    have := Real.log_lt_log (EB5ef.J_pos K hK u c t) ht
    rwa [Real.log_exp] at this
  nlinarith
