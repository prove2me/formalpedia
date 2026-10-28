-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:21:44.403248+00:00
-- url     : https://prove2.me/submissions/4d0c9764-dc43-4b3a-a6d5-43c2484c4fe7

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E,
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
       ∂Qp) =
     Qp E *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
  let D : Set Ω := {ω | T ω < ⊤}
  let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
  let density : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity density
  let M : ℝ≥0∞ := ∫⁻ r : ℝ, (∫⁻ ω,
    density (ω, r) * H (Real.toNNReal r)
      (fun s : ℝ≥0 => X.X s ω) ∂P) ∂(expMeasure p)
  have hunit (r : ℝ) : (∫⁻ ω : Ω, density (ω, r) ∂P) = 1 := by
    have h := (chat04_esscher_weighted_finite_horizon_probability
      X (Real.toNNReal r) θ hθ).measure_univ
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    simpa only [density, SpectrallyNegativeLevy.ψ] using h
  have hMone :
      (∫⁻ r : ℝ, (∫⁻ ω : Ω, density (ω, r) ∂P) ∂(expMeasure p)) = 1 := by
    simp_rw [hunit]
    haveI : IsProbabilityMeasure (expMeasure p) := isProbabilityMeasure_expMeasure hp
    simp
  have hRawOne := avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
    X b hb θ p hθ hp
    (fun (_ : ℝ≥0) (_ : ℝ≥0 → ℝ) => (1 : ℝ≥0∞)) measurable_const
  change (∫⁻ z in E, (1 : ℝ≥0∞) ∂Qp) =
    (∫⁻ ω in D, discount (age ω) ∂P) *
      (∫⁻ r : ℝ, (∫⁻ ω : Ω, density (ω,r) * 1 ∂P) ∂(expMeasure p)) at hRawOne
  simp only [mul_one] at hRawOne
  rw [hMone] at hRawOne
  have hEvent : Qp E = (∫⁻ ω in D, discount (age ω) ∂P) := by
    simpa using hRawOne
  have hRaw := avram_ws01e_b_true_uncapped_firstRecord_Qp_fullPath_regeneration
    X b hb θ p hθ hp H hH
  change (∫⁻ z in E,
    H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
      (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1) ∂Qp) =
    (∫⁻ ω in D, discount (age ω) ∂P) * M at hRaw
  rw [← hEvent] at hRaw
  exact hRaw
