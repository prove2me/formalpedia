-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_capped_killed_Qp_wholePath_regeneration_instantiated
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:06:21.998997+00:00
-- url     : https://prove2.me/submissions/39d83f7a-2956-43ad-a200-84ddd3926fcd

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_capped_killed_record_exact_discount
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_lowerPassage_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_wholePath_stopped_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
import Theorems.Thm_AvramDividend_Classical_firstRecord_truncation_clock_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The lower-killed capped strict record regenerates the true tilted
exponential-clock residual full path under the actual joint density. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2)) :
    (let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let A : Set Ω :=
       {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
       {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
     let W : Ω → ℝ≥0∞ := fun ω => if ω ∈ A then 1 else 0
     let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
       ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
     (∫⁻ z : Ω × ℝ,
       if (τ z.1 : ℝ) ≤ z.2 then
         W z.1 * H (Real.toNNReal (z.2 - (τ z.1 : ℝ)))
           (fun s : ℝ≥0 =>
             X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1)
       else 0
       ∂((P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ))))) =
     (∫⁻ ω, if ω ∈ A then discount (τ ω) else 0 ∂P) *
       (∫⁻ r : ℝ, (∫⁻ ω,
         ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal r) ω -
             (Real.toNNReal r : ℝ) * X.ψ θ)) *
         H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) ∂P)
         ∂(expMeasure p))) := by
  classical
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
  let A : Set Ω :=
    {ω | twoSidedExitUpTime X b ω < twoSidedExitDownTime X lower ω} ∩
    {ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)}
  let W : Ω → ℝ≥0∞ := fun ω => if ω ∈ A then 1 else 0
  let discount : ℝ≥0 → ℝ≥0∞ := fun u =>
    ENNReal.ofReal (Real.exp (θ * b - (p + X.ψ θ) * (u : ℝ)))
  have hτ : Measurable τ := firstRecord_truncation_clock_measurable X b N
  have hUpper : Measurable (twoSidedExitUpTime X b) := by
    have hs := (upperPassage_stopping_rightCont_filtration X b).measurable_iSup
    exact hs.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
  have hLower : Measurable (twoSidedExitDownTime X lower) := by
    have hs := (avram_ws01h_lowerPassage_stopping_rightCont_filtration
      X lower).measurable_iSup
    exact hs.mono (iSup_le fun i => 𝓕.rightCont.le i) le_rfl
  have hA : MeasurableSet A := by
    change MeasurableSet
      ({ω : Ω | twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X lower ω} ∩
       {ω : Ω | twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞)})
    exact (measurableSet_lt hUpper hLower).inter
      (measurableSet_le hUpper measurable_const)
  have hWmeas : Measurable W := by
    change Measurable (fun ω : Ω => if ω ∈ A then (1 : ℝ≥0∞) else 0)
    exact measurable_const.ite hA measurable_const
  have hd : Measurable discount := by
    dsimp [discount]
    fun_prop
  have hHsec (u : ℝ≥0) : Measurable (H u) := by
    have hk : Measurable (fun f : ℝ≥0 → ℝ => (u, f)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using hH.comp hk
  have hRMeas :=
    avram_ws01h_esscher_fullPath_fresh_reward_lintegral_measurable X θ H hH
  have hWeight (ω : Ω) (hω : ω ∈ A) :
      ENNReal.ofReal (Real.exp (-(p * (τ ω : ℝ)))) *
        ENNReal.ofReal (Real.exp
          (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) =
        discount (τ ω) := by
    have hhit : twoSidedExitUpTime X b ω ≤ (N : ℝ≥0∞) := hω.2
    simpa only [τ, discount] using
      avram_ws01h_capped_killed_record_exact_discount
        X b hb N ω θ (X.ψ θ) p rfl hhit
  have hJoint : Measurable (fun z : Ω × ℝ =>
      ENNReal.ofReal (Real.exp
        (θ * X.X (Real.toNNReal z.2) z.1 -
          (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by
    have hX := chat04_levy_joint_time_state_measurable X
    have hu : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) := by
      fun_prop
    have hAtTime : Measurable
        (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
      hX.comp (hu.prodMk measurable_fst)
    fun_prop
  have hPostMeas :=
    avram_ws01h_actual_stopped_post_esscher_fullPath_reward_measurable
      X τ hτ θ H hH
  have hObserve :=
    (avram_ws01e_b_joint_wholePath_stopped_reward_measurable
      X τ hτ H hH W hWmeas).2
  have hReward :=
    avram_ws01e_b_joint_fullPath_postStop_Esscher_reward_measurable
      X τ hτ θ H hH W hWmeas
  have hSplit (ω : Ω) (t : ℝ) (ht : (τ ω : ℝ) ≤ t) :=
    avram_ws01e_b_actual_Qp_real_clock_stopped_density_split
      X θ τ ω t ht
  have hFactor :=
    avram_ws01h_capped_killed_record_esscher_fullpath_clock_factor
      X lower b N θ p hθ hp τ A rfl rfl hτ hA W
      (fun ω => rfl) discount hd hWeight H hHsec hRMeas
      hPostMeas hJoint hObserve hReward hSplit
  simpa only [τ, A, W, discount] using hFactor
