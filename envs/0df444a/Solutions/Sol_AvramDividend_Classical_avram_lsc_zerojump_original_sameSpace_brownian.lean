-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_zerojump_original_sameSpace_brownian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T16:07:17.573745+00:00
-- url     : https://prove2.me/submissions/ee6b1806-020d-42c2-b5f9-0afd4ea2cdd3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_realTime_increment_gaussian
import Theorems.Thm_AvramDividend_Classical_avram_lsc_realTime_centered_increment_indep_past
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Represent the original zero-jump Avram process as a filtered real-time Brownian driver. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        W.W t ω =
          (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ := by
  let w : ℝ → Ω → ℝ := fun t ω =>
    (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ
  have hrepr (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      (fun ω => w t ω - w s ω) =
        (fun ω =>
          ((X.X (Real.toNNReal t) ω - X.X (Real.toNNReal s) ω) -
             (t - s) * X.c) / X.σ) := by
    funext ω
    dsimp [w]
    simp only [Real.coe_toNNReal', max_eq_left hs,
      max_eq_left (hs.trans hst)]
    ring
  have hEval : ∀ t, Measurable (w t) := by
    intro t
    have hXt : Measurable (X.X (Real.toNNReal t)) :=
      (X.adapted _).mono (𝓕.le _) le_rfl
    exact (hXt.sub_const _).div_const _
  have hJoint : Measurable (Function.uncurry w) := by
    change Measurable (fun p : ℝ × Ω =>
      (X.X (Real.toNNReal p.1) p.2 - (Real.toNNReal p.1 : ℝ) * X.c) / X.σ)
    exact (((chat04_levy_joint_time_state_measurable X).comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)).sub
      ((measurable_real_toNNReal.comp measurable_fst).coe_nnreal_real.mul_const
        X.c)).div_const X.σ
  have hCont : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => w t ω) := by
    filter_upwards [avram_ubv_top11_original_zero_nu_global_continuous_ae X hν]
      with ω hω
    exact ((hω.comp continuous_real_toNNReal).sub
      ((NNReal.continuous_coe.comp continuous_real_toNNReal).mul_const
        X.c)).div_const X.σ
  refine ⟨{
      W := w
      measurable_eval := hEval
      joint_measurable := hJoint
      initial_zero := ?_
      increment_gaussian := ?_
      continuous_paths := hCont
      negative_zero := ?_
      joint_increment_independent := ?_
    }, ?_⟩
  · filter_upwards [] with ω
    simp [w, X.X_zero]
  · intro s t hs hst
    have hsource :=
      avram_lsc_zerojump_realTime_increment_gaussian X hν hσ
        s t hs hst.le
    have hclock : Real.toNNReal (t - s) =
        (⟨t - s, sub_nonneg.mpr hst.le⟩ : ℝ≥0) :=
      NNReal.eq (Real.coe_toNNReal _ (sub_nonneg.mpr hst.le))
    simpa only [hrepr s t hs hst.le, hclock] using hsource
  · intro s hs
    filter_upwards [] with ω
    change (X.X (Real.toNNReal s) ω -
      (Real.toNNReal s : ℝ) * X.c) / X.σ = 0
    rw [Real.toNNReal_of_nonpos hs.le]
    simp [X.X_zero]
  · intro s t hs hst
    have hpast :
        (⨆ j ∈ Iic s, MeasurableSpace.comap (w j) inferInstance) ≤
          𝓕 (Real.toNNReal s) := by
      refine iSup_le fun j => iSup_le fun hj => ?_
      have hjX : Measurable[𝓕 (Real.toNNReal s)] (X.X (Real.toNNReal j)) :=
        (X.adapted _).mono (𝓕.mono (Real.toNNReal_le_toNNReal hj))
          le_rfl
      exact Measurable.comap_le ((hjX.sub_const _).div_const _)
    simpa only [hrepr s t hs hst.le] using
      (indep_of_indep_of_le_left
        (avram_lsc_realTime_centered_increment_indep_past
          X s t hs hst.le).symm hpast)
  · intro t ω
    rfl

