-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:27:42.970668+00:00
-- url     : https://prove2.me/submissions/5c17de62-2f65-4b2f-9e4e-1eaa0784f84d

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_open_survival_iff_weak_lower_clock
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The actual fresh terminal Esscher Qp rational-grid full-path reward
is exactly the genuine complete closed lower-survival CDF mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) (x : ℝ) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal z.2 →
           0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1}).indicator
         (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1}).indicator
         (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by
  intro Qp
  let G : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧ ∀ n : ℕ, 0 < n →
    ∀ k : ℕ, (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal z.2 →
      0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1}
  let W : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    ENNReal.ofReal z.2 ≤ twoSidedExitDownTime X (-x) z.1}
  let S : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
    s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1}
  have hGW : G = W := by
    ext z
    change (0 ≤ z.2 ∧ ∀ n : ℕ, 0 < n →
      ∀ k : ℕ, (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal z.2 →
        0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1) ↔
      (0 ≤ z.2 ∧ ENNReal.ofReal z.2 ≤
        twoSidedExitDownTime X (-x) z.1)
    constructor
    · rintro ⟨ht, hg⟩
      refine ⟨ht, ?_⟩
      change (Real.toNNReal z.2 : ℝ≥0∞) ≤
        twoSidedExitDownTime X (-x) z.1
      exact (avram_ws01h_rational_open_survival_iff_weak_lower_clock
        X x z.1 (Real.toNNReal z.2)).mp hg
    · rintro ⟨ht, hw⟩
      refine ⟨ht, ?_⟩
      change (Real.toNNReal z.2 : ℝ≥0∞) ≤
        twoSidedExitDownTime X (-x) z.1 at hw
      exact (avram_ws01h_rational_open_survival_iff_weak_lower_clock
        X x z.1 (Real.toNNReal z.2)).mpr hw
  have hWeak :=
    avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
      X (-x) θ p hθ hp (fun _ => (1 : ℝ≥0∞)) measurable_const
  have hClosed :=
    avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward
      P X p hp θ x (fun _ => (1 : ℝ≥0∞)) measurable_const
  change (∫⁻ z : Ω × ℝ, G.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
    (∫⁻ z : Ω × ℝ, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂Qp)
  rw [hGW]
  let S' : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
    s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
  have hSS : S = S' := by
    ext z
    change (0 ≤ z.2 ∧ ∀ s : ℝ≥0,
      s ≤ Real.toNNReal z.2 → 0 ≤ x + X.X s z.1) ↔
      (0 ≤ z.2 ∧ ∀ s : ℝ≥0,
        s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1)
    constructor
    · rintro ⟨ht, hs⟩
      refine ⟨ht, ?_⟩
      intro s hst
      have h := hs s hst
      linarith
    · rintro ⟨ht, hs⟩
      refine ⟨ht, ?_⟩
      intro s hst
      have h := hs s hst
      linarith
  rw [hSS]
  simpa only [Qp, W, S'] using hWeak.symm.trans hClosed
