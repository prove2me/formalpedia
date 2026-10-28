-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_first_record_true_terminal_esscher_exp_clock_mass_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T11:45:58.244824+00:00
-- url     : https://prove2.me/submissions/f60d6c08-644f-413b-93b3-5e06e1d6155a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_exp_clock_random_age_joint_reward_shift_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_capped_first_record_esscher_future_lag_normalisation_ws01d
import Theorems.Thm_AvramDividend_Classical_firstRecord_capped_clock_eq_uncapped_of_le_horizon
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_chat08_upper_passage_clock_measurable
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact finite-cap mass of a first upper record under the genuine
random-terminal Esscher density on P × Exp(p). The real clock stays real. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (p : ℝ) (hp : 0 < p)
    (phi q : ℝ) (hphi : 0 ≤ phi) (hroot : X.ψ phi = q) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
     (∫⁻ z : Ω × ℝ,
       if z.1 ∈ A ∧ (τ z.1 : ℝ) ≤ z.2 then
         ENNReal.ofReal (Real.exp
           (phi * X.X z.2.toNNReal z.1 -
             (z.2.toNNReal : ℝ) * q))
       else 0 ∂(P.prod (ProbabilityTheory.expMeasure p))) =
     (∫⁻ ω : Ω, if ω ∈ A then
       ENNReal.ofReal (Real.exp
         (phi * b - (p + q) * (τ ω : ℝ)))
       else 0 ∂P)) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let τ : Ω → ℝ≥0 := fun ω => (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω := {ω : Ω | twoSidedExitUpTime X b ω < (N : ℝ≥0∞)}
  let discount : ℝ≥0 → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (phi * b - (p + q) * (s : ℝ)))
  let Lag : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp
    (phi * (X.X (τ z.1 + z.2.toNNReal) z.1 - X.X (τ z.1) z.1) -
      (z.2.toNNReal : ℝ) * q))
  let K : Ω × ℝ → ℝ≥0∞ := fun z => if z.1 ∈ A then discount (τ z.1) * Lag z else 0
  let R : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (p * (τ z.1 : ℝ))) * K z
  let L : Ω × ℝ → ℝ≥0∞ := fun z =>
    if z.1 ∈ A ∧ (τ z.1 : ℝ) ≤ z.2 then
      ENNReal.ofReal (Real.exp (phi * X.X z.2.toNNReal z.1 -
        (z.2.toNNReal : ℝ) * q)) else 0
  have hτ : Measurable τ := firstRecord_truncation_clock_measurable X b N
  have hτreal : Measurable (fun ω : Ω => (τ ω : ℝ)) := hτ.coe_nnreal_real
  have hA : MeasurableSet A := by
    dsimp [A]; exact measurableSet_lt
      (chat08_upper_passage_clock_measurable X b) measurable_const
  have hX : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2) :=
    chat04_levy_joint_time_state_measurable X
  have hT : Measurable (fun z : Ω × ℝ => τ z.1 + z.2.toNNReal) :=
    (hτ.comp measurable_fst).add (measurable_real_toNNReal.comp measurable_snd)
  have hXt : Measurable (fun z : Ω × ℝ => X.X (τ z.1 + z.2.toNNReal) z.1) :=
    hX.comp (hT.prodMk measurable_fst)
  have hXτ : Measurable (fun z : Ω × ℝ => X.X (τ z.1) z.1) :=
    hX.comp ((hτ.comp measurable_fst).prodMk measurable_fst)
  have hLag : Measurable Lag := by
    dsimp [Lag]; exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (hXt.sub hXτ)).sub
          ((measurable_real_toNNReal.comp measurable_snd).coe_nnreal_real.mul measurable_const)))
  have hd : Measurable discount := by
    dsimp [discount]; exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.sub (measurable_const.mul measurable_subtype_coe)))
  have hK : Measurable K := by
    dsimp [K]; exact ((hd.comp (hτ.comp measurable_fst)).mul hLag).ite
      (hA.preimage measurable_fst) measurable_const
  have hR : Measurable R := by
    dsimp [R]; exact (ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        (measurable_const.mul (hτreal.comp measurable_fst)))).mul hK
  have hHit (ω : Ω) (hω : ω ∈ A) : X.X (τ ω) ω = b := by
    have hclock : ((τ ω : ℝ≥0) : ℝ≥0∞) = twoSidedExitUpTime X b ω :=
      firstRecord_capped_clock_eq_uncapped_of_le_horizon X b N ω (le_of_lt hω)
    have hInf : ((τ ω : ℝ≥0) : ℝ≥0∞) =
        (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)) := by
      simpa only [twoSidedExitUpTime] using hclock
    exact firstUpcrossing_value_eq_threshold X b hb ω (τ ω) hInf
  have hTime (ω : Ω) (t : ℝ) (ht : (τ ω : ℝ) ≤ t) : τ ω + (t - (τ ω : ℝ)).toNNReal = t.toNNReal := by
    apply Subtype.ext
    change (τ ω : ℝ) + ((t - (τ ω : ℝ)).toNNReal : ℝ) = (t.toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr ht),
      Real.coe_toNNReal _ (le_trans (τ ω).property ht)]
    ring
  have hCancel (ω : Ω) (u : ℝ) : ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) * R (ω, u) = K (ω, u) := by
    dsimp [R]; rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    have hz : Real.exp (-(p * (τ ω : ℝ))) * Real.exp (p * (τ ω : ℝ)) = 1 := by
      rw [← Real.exp_add]; have hzero : -(p * (τ ω : ℝ)) + p * (τ ω : ℝ) = 0 := by ring
      rw [hzero, Real.exp_zero]
    rw [hz]; simp
  have hPoint (ω : Ω) (t : ℝ) : L (ω, t) = (if (τ ω : ℝ) ≤ t then R (ω, t - (τ ω : ℝ)) else 0) := by
    by_cases hω : ω ∈ A
    · by_cases ht : (τ ω : ℝ) ≤ t
      · have htime := hTime ω t ht
        have hhit := hHit ω hω
        simp only [L, R, K, Lag, discount, hω, ht, and_self, if_pos, true_and]
        rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
          ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt (Real.exp_pos _))
            (le_of_lt (Real.exp_pos _)))]
        congr 1
        repeat rw [← Real.exp_add]
        congr 1
        have hsub : ((t - (τ ω : ℝ)).toNNReal : ℝ) = t - (τ ω : ℝ) :=
          Real.coe_toNNReal _ (sub_nonneg.mpr ht)
        rw [← htime, hhit, hsub, htime,
          Real.coe_toNNReal _ (le_trans (τ ω).property ht)]; ring
      · simp [L, R, K, hω, ht]
    · simp [L, R, K, hω]
  change (∫⁻ z : Ω × ℝ, L z ∂(P.prod (ProbabilityTheory.expMeasure p))) = _
  calc
    _ = (∫⁻ z : Ω × ℝ, if (τ z.1 : ℝ) ≤ z.2 then
          R (z.1, z.2 - (τ z.1 : ℝ)) else 0
          ∂(P.prod (ProbabilityTheory.expMeasure p))) := by
      congr 1; funext z; exact hPoint z.1 z.2
    _ = (∫⁻ ω : Ω, ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
          (∫⁻ u : ℝ, R (ω, u) ∂(ProbabilityTheory.expMeasure p)) ∂P) :=
      exp_clock_random_age_joint_reward_shift_ws01d P p hp τ hτ R hR
    _ = (∫⁻ ω : Ω, (∫⁻ u : ℝ, K (ω, u)
          ∂(ProbabilityTheory.expMeasure p)) ∂P) := by
      congr 1; funext ω
      exact (lintegral_const_mul _
        (hR.comp (measurable_const.prodMk measurable_id))).symm.trans
          (lintegral_congr (fun u => hCancel ω u))
    _ = (∫⁻ z : Ω × ℝ, K z ∂(P.prod (ProbabilityTheory.expMeasure p))) :=
      (lintegral_prod K hK.aemeasurable).symm
    _ = (∫⁻ u : ℝ, (∫⁻ ω : Ω, K (ω, u) ∂P) ∂(ProbabilityTheory.expMeasure p)) :=
      lintegral_prod_symm K hK.aemeasurable
    _ = (∫⁻ u : ℝ, (∫⁻ ω : Ω, if ω ∈ A then discount (τ ω) else 0 ∂P)
          ∂(ProbabilityTheory.expMeasure p)) := by
      congr 1; funext u
      simpa only [K, Lag, discount, τ, A] using
        (levy_capped_first_record_esscher_future_lag_normalisation_ws01d
          X b N u.toNNReal phi q hphi hroot discount hd)
    _ = _ := by
      rw [lintegral_const, measure_univ, mul_one]
