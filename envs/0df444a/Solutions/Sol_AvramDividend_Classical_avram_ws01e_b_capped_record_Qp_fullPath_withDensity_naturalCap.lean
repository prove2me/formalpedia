-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_capped_record_Qp_fullPath_withDensity_naturalCap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:32:31.584181+00:00
-- url     : https://prove2.me/submissions/61b12232-66a3-46b4-adfa-30e483468257

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 ≤ b) (n : ℕ)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let D : Set Ω := {ω | T ω < (n : ℝ≥0∞)}
     let E : Set (Ω × ℝ) :=
       {z | T z.1 < (n : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2}
     let W : ℝ≥0 → ℝ≥0∞ :=
       fun u => ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     let K : Ω × ℝ → ℝ≥0∞ := fun z =>
       H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
         (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
     (Qp.withDensity K) E =
       (P.withDensity (fun ω => W (age ω))) D *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let D : Set Ω := {ω | T ω < (n : ℝ≥0∞)}
  let E : Set (Ω × ℝ) := {z | T z.1 < (n : ℝ≥0∞) ∧ (age z.1 : ℝ) ≤ z.2}
  let W : ℝ≥0 → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 - (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let K : Ω × ℝ → ℝ≥0∞ := fun z => H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
    (fun s : ℝ≥0 => X.X (age z.1 + s) z.1 - X.X (age z.1) z.1)
  let M : ℝ≥0∞ := ∫⁻ r : ℝ, (∫⁻ ω,
    ENNReal.ofReal (Real.exp (θ * X.X (Real.toNNReal r) ω -
      (Real.toNNReal r : ℝ) * X.ψ θ)) *
    H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P) ∂(expMeasure p)
  let τ : Ω → ℝ≥0 := fun ω => (min (T ω) (n : ℝ≥0∞)).toNNReal
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge : Measurable age := hT.ennreal_toNNReal
  have hD : MeasurableSet D := measurableSet_lt hT measurable_const
  have hE : MeasurableSet E := (measurableSet_lt (hT.comp measurable_fst)
    measurable_const).inter (measurableSet_le (hAge.coe_nnreal_real.comp measurable_fst) measurable_snd)
  have hc := avram_ws01e_b_true_capped_firstRecord_Qp_fullPath_regeneration_instantiated X b hb (n : ℝ≥0) θ p hθ hp H hH
  change (∫⁻ z : Ω × ℝ, if (τ z.1 : ℝ) ≤ z.2 then
    (if z.1 ∈ D then 1 else 0) *
      H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
        (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
    else 0 ∂Qp) = (∫⁻ ω, if ω ∈ D then W (τ ω) else 0 ∂P) * M at hc
  change (Qp.withDensity K) E = (P.withDensity (fun ω => W (age ω))) D * M
  rw [withDensity_apply K hE, withDensity_apply (fun ω => W (age ω)) hD]
  rw [← lintegral_indicator hE K, ← lintegral_indicator hD (fun ω => W (age ω))]
  convert hc using 1
  · apply lintegral_congr
    intro z
    by_cases ha : T z.1 < (n : ℝ≥0∞)
    · simp [Set.indicator, D, E, K, age, τ, ha, min_eq_left (le_of_lt ha)]
    · simp [Set.indicator, D, E, ha]
  · congr 1
    apply lintegral_congr
    intro ω
    by_cases ha : T ω < (n : ℝ≥0∞)
    · simp [Set.indicator, D, W, age, τ, ha, min_eq_left (le_of_lt ha)]
    · simp [Set.indicator, D, ha]
