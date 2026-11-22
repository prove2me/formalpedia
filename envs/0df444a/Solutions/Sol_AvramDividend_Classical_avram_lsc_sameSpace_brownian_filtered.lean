-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsc_sameSpace_brownian_filtered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T16:02:24.694435+00:00
-- url     : https://prove2.me/submissions/2fca9558-967f-46d5-83ba-0944a1a3b57d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
open MeasureTheory ProbabilityTheory Set LevyStochCalc.Brownian AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Prove the exact filtered Brownian interface on the original Avram probability space. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hW : ∀ (t : ℝ) (ω : Ω),
      W.W t ω =
        (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ) :
    ∃ ℱr : Filtration ℝ mΩ,
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration W ℱr := by
  let ℱr : Filtration ℝ mΩ := {
    seq := fun t => 𝓕.rightCont (Real.toNNReal t)
    mono' := fun s t hst =>
      𝓕.rightCont.mono (Real.toNNReal_le_toNNReal hst)
    le' := fun t => 𝓕.rightCont.le _
  }
  refine ⟨ℱr, fun _ => rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · intro t
    have hXt : Measurable[𝓕.rightCont (Real.toNNReal t)]
        (X.X (Real.toNNReal t)) :=
      (X.adapted _).mono (𝓕.le_rightCont _) le_rfl
    have htEq : W.W t = fun ω =>
        (X.X (Real.toNNReal t) ω - (Real.toNNReal t : ℝ) * X.c) / X.σ :=
      funext (hW t)
    change Measurable[𝓕.rightCont (Real.toNNReal t)] (W.W t)
    rw [htEq]
    exact (hXt.sub_const _).div_const _
  · intro s hs
    change Indep (𝓕.rightCont (Real.toNNReal s))
      (⨆ t ∈ Set.Ioi s,
        MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) P
    let K : Ω → ℝ≥0 → ℝ := fun ω u =>
      X.X (Real.toNNReal s + u) ω - X.X (Real.toNNReal s) ω
    have hind : Indep (𝓕.rightCont (Real.toNNReal s))
        (MeasurableSpace.comap K inferInstance) P :=
      avram_ja18h_original_future_path_indep_rightcont X (Real.toNNReal s)
    have hfuture :
        (⨆ t ∈ Set.Ioi s,
          MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) ≤
        MeasurableSpace.comap K inferInstance := by
      refine iSup_le fun t => iSup_le fun ht => ?_
      have ht0 : 0 ≤ t := le_trans hs (le_of_lt ht)
      have hδ0 : 0 ≤ t - s := sub_nonneg.mpr (le_of_lt ht)
      have htime : Real.toNNReal s + Real.toNNReal (t - s) =
          Real.toNNReal t := by
        rw [← Real.toNNReal_add hs hδ0]
        congr 1
        ring
      have hKmeas : Measurable[MeasurableSpace.comap K inferInstance] K :=
        Measurable.of_comap_le le_rfl
      have hEval : Measurable[MeasurableSpace.comap K inferInstance]
          (fun ω => K ω (Real.toNNReal (t - s))) :=
        (measurable_pi_apply (Real.toNNReal (t - s))).comp hKmeas
      have hEq : (fun ω => W.W t ω - W.W s ω) =
          (fun ω => (K ω (Real.toNNReal (t - s)) -
            (t - s) * X.c) / X.σ) := by
        funext ω
        rw [hW t ω, hW s ω]
        dsimp [K]
        rw [htime]
        simp only [Real.coe_toNNReal', max_eq_left hs, max_eq_left ht0]
        ring
      have hMeas : Measurable[MeasurableSpace.comap K inferInstance]
          (fun ω => W.W t ω - W.W s ω) := by
        rw [hEq]
        exact (hEval.sub_const _).div_const _
      exact Measurable.comap_le hMeas
    exact indep_of_indep_of_le_right hind hfuture
