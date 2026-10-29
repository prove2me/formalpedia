-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_Qp_runningSup_terminalDrawdown_indepFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:05:31.629004+00:00
-- url     : https://prove2.me/submissions/d663526e-7b73-41fe-a2f5-83accf2aface

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_upper_ray_cylinders_indepFun
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
import Theorems.Thm_AvramDividend_Classical_levyPath_bddAbove_Icc
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
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
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) :
    ProbabilityTheory.IndepFun
      (fun z : Ω × ℝ => runningSup X (Real.toNNReal z.2) z.1)
      (fun z : Ω × ℝ =>
        runningSup X (Real.toNNReal z.2) z.1 -
          X.X (Real.toNNReal z.2) z.1)
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))) := by
  classical
  let Qp : Measure (Ω × ℝ) := (P.prod (expMeasure p)).withDensity
    (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
  let S : Ω × ℝ → ℝ := fun z => runningSup X (Real.toNNReal z.2) z.1
  let D : Ω × ℝ → ℝ := fun z => S z - X.X (Real.toNNReal z.2) z.1
  haveI : IsProbabilityMeasure Qp :=
    chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X θ p hθ hp hJoint
  have hS : Measurable S := by
    simpa only [S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  have hD : Measurable D := by
    simpa only [D, S] using
      (levy_exponential_real_clock_extrema_drawdown_measurable X).snd
  change IndepFun S D Qp
  apply avram_ws01e_b_upper_ray_cylinders_indepFun Qp S hS D hD
  intro b B hB
  by_cases hb : 0 ≤ b
  ·
    let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
    let age : Ω → ℝ≥0 := fun ω => (T ω).toNNReal
    let E : Set (Ω × ℝ) := {z | T z.1 < ⊤ ∧ (age z.1 : ℝ) ≤ z.2}
    let A : Set (Ω × ℝ) := {z | b < S z}
    rcases avram_ws01e_bi_new_exists_measurable_fullpath_drawdown_proxy X with
      ⟨F, hProxyMeas, hFreshProxy, hShiftProxy⟩
    let H (t : ℝ≥0) (f : ℝ≥0 → ℝ) : ℝ≥0∞ :=
      if F t f ∈ B then 1 else 0
    have hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) => H z.1 z.2) :=
      Measurable.ite (hB.preimage hProxyMeas) measurable_const measurable_const
    have hFresh (ω : Ω) (r : ℝ) :
        H (Real.toNNReal r) (fun s : ℝ≥0 => X.X s ω) =
          B.indicator (fun _ => (1 : ℝ≥0∞)) (D (ω, r)) := by
      dsimp [H, D, S]
      rw [hFreshProxy ω (Real.toNNReal r)]
      simp only [Set.indicator]
    have hReset (z : Ω × ℝ) (hz : z ∈ E) :
        H (Real.toNNReal (z.2 - (age z.1 : ℝ)))
          (fun s : ℝ≥0 =>
            X.X (age z.1 + s) z.1 - X.X (age z.1) z.1) =
          B.indicator (fun _ => (1 : ℝ≥0∞)) (D z) := by
      rcases hz with ⟨hFinite, hObsReal⟩
      let e : ℝ≥0 := Real.toNNReal z.2
      have hu : (age z.1 : ℝ≥0∞) = T z.1 := by
        dsimp [age]
        exact ENNReal.coe_toNNReal (ne_top_of_lt hFinite)
      have hPos : 0 ≤ z.2 := le_trans (NNReal.coe_nonneg _) hObsReal
      have he : (e : ℝ) = z.2 := Real.coe_toNNReal _ hPos
      have hObs : age z.1 ≤ e := by
        exact_mod_cast (show (age z.1 : ℝ) ≤ (e : ℝ) by
          rw [he]
          exact hObsReal)
      have hDelta : Real.toNNReal (z.2 - (age z.1 : ℝ)) =
          e - age z.1 := by
        apply NNReal.coe_injective
        rw [NNReal.coe_sub hObs,
          Real.coe_toNNReal _ (sub_nonneg.mpr hObsReal), he]
      have hAdd : age z.1 + (e - age z.1) = e :=
        add_tsub_cancel_of_le hObs
      have hFutureBdd :
          BddAbove ((fun r : ℝ≥0 => X.X (age z.1 + r) z.1) ''
            Set.Icc 0 (e - age z.1)) := by
        apply (levyPath_bddAbove_Icc X z.1 e).mono
        rintro y ⟨r, hr, rfl⟩
        refine ⟨age z.1 + r, ⟨zero_le, ?_⟩, rfl⟩
        calc
          age z.1 + r ≤ age z.1 + (e - age z.1) :=
            add_le_add_right hr.2 _
          _ = e := hAdd
      have hDReset :=
        avram_ws01e_b_firstRecord_drawdown_normalised_at_clock
          X b hb z.1 (age z.1) hu
          (levyPath_bddAbove_Icc X z.1 (age z.1))
          (fun _ : Unit => e) () hObs hFutureBdd
      dsimp [H, D, S]
      rw [hDelta, hShiftProxy z.1 (age z.1) (e - age z.1), hAdd]
      simp only [Set.indicator]
      exact congrArg (fun d : ℝ => if d ∈ B then (1 : ℝ≥0∞) else 0)
        hDReset.symm
    have hFactorE :=
      avram_ws01e_bi_new_Qp_record_arbitrary_borel_reward_factor
        X θ p hθ hp hJoint b hb D hD B hB E rfl H hH hFresh hReset
    change Qp (E ∩ D ⁻¹' B) = Qp E * Qp (D ⁻¹' B) at hFactorE
    have hAE :=
      avram_ws01e_bi_new_record_upper_ray_ae_true_Qp
        X θ p hθ hp hJoint b hb
    change A =ᵐ[Qp] E at hAE
    have hRestrict : Qp.restrict A = Qp.restrict E :=
      Measure.restrict_congr_set hAE
    have hMass : Qp A = Qp E := by
      calc
        Qp A = (Qp.restrict A) Set.univ := by simp
        _ = (Qp.restrict E) Set.univ := by rw [hRestrict]
        _ = Qp E := by simp
    have hDB : MeasurableSet (D ⁻¹' B) := hB.preimage hD
    have hInter : Qp (A ∩ D ⁻¹' B) = Qp (E ∩ D ⁻¹' B) := by
      calc
        Qp (A ∩ D ⁻¹' B) = (Qp.restrict A) (D ⁻¹' B) := by
          rw [Measure.restrict_apply hDB, Set.inter_comm]
        _ = (Qp.restrict E) (D ⁻¹' B) := by rw [hRestrict]
        _ = Qp (E ∩ D ⁻¹' B) := by
          rw [Measure.restrict_apply hDB, Set.inter_comm]
    change Qp (A ∩ D ⁻¹' B) = Qp A * Qp (D ⁻¹' B)
    rw [hInter, hMass]
    exact hFactorE
  · have hbNeg : b < 0 := lt_of_not_ge hb
    have hAll : S ⁻¹' Set.Ioi b = (Set.univ : Set (Ω × ℝ)) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le hbNeg
        (runningSup_eq_rawSup_nonneg X (Real.toNNReal z.2) z.1).2
    simp only [hAll, Set.univ_inter, measure_univ, one_mul]