-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_regenerative_reward_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T21:44:08.294621+00:00
-- url     : https://prove2.me/submissions/ff045051-45a8-4d36-8b9f-c374e68d1997

import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
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
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (W : Ω × ℝ → ℝ≥0∞) (hW : Measurable W)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2))
    (hFresh : ∀ (ω : Ω) (r : ℝ),
      W (ω, r) = H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω))
    (hReset : ∀ (z : Ω × ℝ),
      twoSidedExitUpTime X b z.1 < ⊤ →
      ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2 →
      W z =
        H (Real.toNNReal (z.2 -
            ((twoSidedExitUpTime X b z.1).toNNReal : ℝ)))
          (fun s : ℝ≥0 =>
            X.X ((twoSidedExitUpTime X b z.1).toNNReal + s) z.1 -
            X.X (twoSidedExitUpTime X b z.1).toNNReal z.1)) :
    (let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
     let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
     let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
     let Qp : Measure (Ω × ℝ) := (P.prod (ProbabilityTheory.expMeasure p)).withDensity
       (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
         (θ * X.X (Real.toNNReal z.2) z.1 -
           (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z in E, W z ∂Qp) =
       Qp E * (∫⁻ z : Ω × ℝ, W z ∂Qp)) := by
  classical
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
  let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
  let density : Ω × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp
      (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity density
  let M : ℝ≥0∞ := ∫⁻ r : ℝ, (∫⁻ ω : Ω,
    density (ω, r) * H (Real.toNNReal r)
      (fun s : ℝ≥0 => X.X s ω) ∂P) ∂(expMeasure p)
  haveI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hProd : Measurable (fun z : Ω × ℝ => density z * W z) :=
    hJoint.mul hW
  have hM : M = (∫⁻ z : Ω × ℝ, W z ∂Qp) := by
    calc
      M = (∫⁻ r : ℝ, (∫⁻ ω : Ω,
          density (ω, r) * W (ω, r) ∂P) ∂(expMeasure p)) := by
        dsimp [M]
        congr 1
        funext r
        congr 1
        funext ω
        rw [hFresh ω r]
      _ = ∫⁻ z : Ω × ℝ, density z * W z ∂(P.prod (expMeasure p)) := by
        exact (MeasureTheory.lintegral_prod_symm
          (fun z : Ω × ℝ => density z * W z) hProd.aemeasurable).symm
      _ = ∫⁻ z : Ω × ℝ, W z ∂Qp := by
        rw [lintegral_withDensity_eq_lintegral_mul
          (P.prod (expMeasure p)) hJoint hW]
        rfl
  have hT : Measurable T := chat08_upper_passage_clock_measurable X b
  have hAge : Measurable age := hT.ennreal_toNNReal
  have hE : MeasurableSet E :=
    (measurableSet_lt (hT.comp measurable_fst) measurable_const).inter
      (measurableSet_le ((hAge.coe_nnreal_real).comp measurable_fst)
        measurable_snd)
  have hReg :=
    avram_ws01e_b_uncapped_firstRecord_Qp_conditional_regeneration
      X b hb θ p hθ hp H hH
  change (∫⁻ z in E,
      H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
        (fun s : ℝ≥0 =>
          X.X (age z.1 + s) z.1 - X.X (age z.1) z.1) ∂Qp) =
    Qp E * M at hReg
  change (∫⁻ z in E, W z ∂Qp) =
    Qp E * (∫⁻ z, W z ∂Qp)
  calc
    _ = (∫⁻ z in E,
        H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
          (fun s : ℝ≥0 =>
            X.X (age z.1 + s) z.1 - X.X (age z.1) z.1) ∂Qp) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem hE] with z hz
      exact hReset z hz.1 hz.2
    _ = Qp E * M := hReg
    _ = _ := by rw [hM]
