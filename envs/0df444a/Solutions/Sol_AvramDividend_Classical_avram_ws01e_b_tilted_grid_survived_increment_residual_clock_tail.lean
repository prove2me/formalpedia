-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_tilted_grid_survived_increment_residual_clock_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:13:24.509786+00:00
-- url     : https://prove2.me/submissions/6f61fc36-9fb3-4afb-a2aa-dc4ecfc1d625

import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_support_finite_grid_full_clock_event_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exp_clock_toNNReal_strict_tail
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_exponential_nnreal_survival_memorylessness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- Actual tilted joint-law Exp(p) residual survival after a stopped increment,
including finite-grid adapted history and the increment's Borel event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0) (u r : ℝ≥0)
    (A : Set Ω)
    (hHistory : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 s) (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hAdapted : ∀ s ∈ grid,
      @MeasurableSet Ω (𝓕 (s + u))
        ((A ∩ {ω : Ω | τ ω = s}) ∩
          (fun ω : Ω => X.X (s + u) ω - X.X s ω) ⁻¹' B))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    let QP : Measure (Ω × ℝ) :=
      ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
        ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    let E : ℝ≥0 → Set (Ω × ℝ) := fun a =>
      {z : Ω × ℝ |
        z.1 ∈ A ∧ τ z.1 ∈ grid ∧
        X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
        (τ z.1 + u) + a < Real.toNNReal z.2}
    QP (E r) =
      ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) * QP (E 0) := by
  let QP : Measure (Ω × ℝ) :=
    ((P.prod (expMeasure p)).withDensity (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
  let E : ℝ≥0 → Set (Ω × ℝ) := fun a =>
    {z : Ω × ℝ |
      z.1 ∈ A ∧ τ z.1 ∈ grid ∧
      X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1 ∈ B ∧
      (τ z.1 + u) + a < Real.toNNReal z.2}
  let C : ℝ≥0 → ℝ≥0 → Set ℝ := fun a s =>
    {t : ℝ | (s + u) + a < Real.toNNReal t}
  let W : ℝ≥0 → ℝ≥0∞ := fun s =>
    ((P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
        (A ∩ {ω : Ω | τ ω = s}) *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
        ((X.X u) ⁻¹' B))
  change QP (E r) =
    ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) * QP (E 0)
  have hEvent (a : ℝ≥0) :
      QP (E a) = ∑ s ∈ grid, W s * (expMeasure p) (C a s) := by
    have hC : ∀ s ∈ grid, MeasurableSet (C a s) := by
      intro s hs
      change MeasurableSet (Real.toNNReal ⁻¹' Ioi ((s + u) + a))
      exact measurable_real_toNNReal measurableSet_Ioi
    have hClockTail : ∀ s ∈ grid, ∀ t ∈ C a s,
        s + u ≤ Real.toNNReal t := by
      intro s hs t ht
      exact le_trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ a by positivity))
        (le_of_lt ht)
    have hBase :=
      avram_ws01e_b_support_finite_grid_full_clock_event_factor
        X θ p hθ hp τ grid u A hHistory B hB hAdapted
        (C a) hC hClockTail hJoint
    simpa only [QP, E, C, W, Set.mem_setOf_eq] using hBase
  have hClock (s : ℝ≥0) :
      (expMeasure p) (C r s) =
        ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) *
          (expMeasure p) (C 0 s) := by
    change (expMeasure p) {t : ℝ | (s + u) + r < Real.toNNReal t} =
      ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) *
        (expMeasure p) {t : ℝ | (s + u) + 0 < Real.toNNReal t}
    simp only [add_zero]
    rw [avram_ws01e_b_exp_clock_toNNReal_strict_tail p hp ((s + u) + r),
      avram_ws01e_b_exp_clock_toNNReal_strict_tail p hp (s + u)]
    exact avram_ws01e_b_exponential_nnreal_survival_memorylessness
      p hp (s + u) r
  rw [hEvent r, hEvent 0]
  calc
    (∑ s ∈ grid, W s * (expMeasure p) (C r s)) =
        ∑ s ∈ grid,
          ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) *
            (W s * (expMeasure p) (C 0 s)) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hClock s]
      ac_rfl
    _ = ENNReal.ofReal (Real.exp (-(p * (r : ℝ)))) *
          (∑ s ∈ grid, W s * (expMeasure p) (C 0 s)) := by
      rw [Finset.mul_sum]
