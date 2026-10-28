-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_first_record_esscher_fresh_exp_lag_normalisation_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:22:56.893015+00:00
-- url     : https://prove2.me/submissions/60f1205f-6fda-428d-9bb1-07d05b7328c5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_future_lag_normalisation_ws01d
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The normalised future Esscher factor has expectation one when its lag is
a fresh, genuinely independent real exponential clock, even after weighting
an uncensored capped first upper record by any measurable stopped-age discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (N : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ z : Ω × ℝ, if z.1 ∈ A then discount (τ z.1) *
       ENNReal.ofReal (Real.exp
         (phi * (X.X (τ z.1 + z.2.toNNReal) z.1 -
            X.X (τ z.1) z.1) -
          (z.2.toNNReal : ℝ) * q)) else 0
       ∂(P.prod (ProbabilityTheory.expMeasure p))) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω :=
    {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
  let F : Ω × ℝ → ℝ≥0∞ := fun z =>
    if z.1 ∈ A then discount (τ z.1) *
      ENNReal.ofReal (Real.exp
        (phi * (X.X (τ z.1 + z.2.toNNReal) z.1 -
          X.X (τ z.1) z.1) -
         (z.2.toNNReal : ℝ) * q)) else 0
  have hτ : Measurable τ :=
    firstRecord_truncation_clock_measurable X b N
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt
      (chat08_upper_passage_clock_measurable X b) measurable_const
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hT : Measurable (fun z : Ω × ℝ =>
      τ z.1 + z.2.toNNReal) :=
    (hτ.comp measurable_fst).add
      (measurable_real_toNNReal.comp measurable_snd)
  have hXt : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1 + z.2.toNNReal) z.1) :=
    hX.comp (hT.prodMk measurable_fst)
  have hXτ : Measurable (fun z : Ω × ℝ =>
      X.X (τ z.1) z.1) :=
    hX.comp ((hτ.comp measurable_fst).prodMk measurable_fst)
  have hR : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (phi * (X.X (τ z.1 + z.2.toNNReal) z.1 -
          X.X (τ z.1) z.1) -
          (z.2.toNNReal : ℝ) * q))) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hXt.sub hXτ)).sub
          ((measurable_real_toNNReal.comp measurable_snd).coe_nnreal_real.mul
            measurable_const)))
  have hF : Measurable F := by
    dsimp [F]
    exact ((hd.comp (hτ.comp measurable_fst)).mul hR).ite
      (hA.preimage measurable_fst) measurable_const
  have hInner (u : ℝ) :
      (∫⁻ ω : Ω, F (ω, u) ∂P) =
      (∫⁻ ω : Ω, if ω ∈ A then discount (τ ω) else 0 ∂P) := by
    simpa only [F, τ, A] using
      (levy_capped_first_record_esscher_future_lag_normalisation_ws01d
        X b N u.toNNReal phi q hphi hroot discount hd)
  change (∫⁻ z : Ω × ℝ, F z
    ∂(P.prod (ProbabilityTheory.expMeasure p))) = _
  calc
    _ = (∫⁻ u : ℝ, (∫⁻ ω : Ω, F (ω, u) ∂P)
         ∂(ProbabilityTheory.expMeasure p)) :=
      lintegral_prod_symm F hF.aemeasurable
    _ = (∫⁻ u : ℝ,
         (∫⁻ ω : Ω, if ω ∈ A then discount (τ ω) else 0 ∂P)
         ∂(ProbabilityTheory.expMeasure p)) := by
      congr 1
      funext u
      exact hInner u
    _ = _ := by
      rw [lintegral_const, measure_univ, mul_one]
