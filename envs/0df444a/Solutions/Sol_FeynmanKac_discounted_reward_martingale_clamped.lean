-- Prove2me | solution 1 for FeynmanKac.discounted_reward_martingale_clamped
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:57:48.297624+00:00
-- url     : https://prove2.me/submissions/8abb7013-b2be-4a31-b2aa-fbe63c720a0f

import Definitions.Def_FeynmanKac_ModelReward
import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
import Theorems.Thm_FeynmanKac_discounted_reward_ito_identity
import Mathlib

namespace S87K

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal

section Prog
variable {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

lemma cont_pair : Continuous fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_fst
  · exact continuous_snd

lemma prog_time {Y : ℝ → Ω → Fin 2 → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYa : ∀ t, Measurable[ℱ t] (Y t)) {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => g s (Y s ω 0)) := by
  let Z : ℝ → Ω → Fin 2 → ℝ := fun s ω => ![Y s ω 0, s]
  have hZc : ∀ ω, Continuous fun t => Z t ω := fun ω =>
    cont_pair.comp (((continuous_apply 0).comp (hYc ω)).prodMk continuous_id)
  have hZa : ∀ t, Measurable[ℱ t] (Z t) := by
    intro t
    have hp2 : Continuous fun y : Fin 2 → ℝ => ((y 0, t) : ℝ × ℝ) :=
      (continuous_apply 0).prodMk continuous_const
    have hc : Continuous fun y : Fin 2 → ℝ => (![y 0, t] : Fin 2 → ℝ) := cont_pair.comp hp2
    exact hc.measurable.comp (hYa t)
  have hpair : Continuous fun z : Fin 2 → ℝ => ((z 1, z 0) : ℝ × ℝ) :=
    (continuous_apply 1).prodMk (continuous_apply 0)
  have hcg : Continuous fun z : Fin 2 → ℝ => g (z 1) (z 0) := hg.comp hpair
  have := ItoLemma.continuous_adapted_composition_progressive hZc hZa hcg
  simpa [Z] using this

lemma meas_time {Y : ℝ → Ω → Fin 2 → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYm : ∀ t, Measurable (Y t)) {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    Measurable (Function.uncurry fun ω s => g s (Y s ω 0)) := by
  have hj : Measurable (fun q : Ω × ℝ => Y q.2 q.1) :=
    (measurable_uncurry_of_continuous_of_measurable hYc hYm).comp measurable_swap
  have : Measurable fun q : Ω × ℝ => ((q.2, Y q.2 q.1 0) : ℝ × ℝ) :=
    measurable_snd.prodMk ((measurable_pi_apply 0).comp hj)
  exact hg.measurable.comp this

lemma prog_det {c : ℝ → ℝ} (hc : Measurable c) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) s => c s) := by
  intro t
  have h : Measurable ((Set.Iic t).indicator c) := hc.indicator measurableSet_Iic
  exact (h.comp (@measurable_snd Ω ℝ (ℱ t) _)).stronglyMeasurable

end Prog

section ModelFacts
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma vol_eq (m : FeynmanKac.BoundedDiffusionModel P) (x t : ℝ) :
    m.volatility x t = m.augmentedVolatility ![x, t] 0 0 := by
  rw [m.augmentedVolatility_space]; simp

lemma vol_cont (m : FeynmanKac.BoundedDiffusionModel P) :
    Continuous fun p : ℝ × ℝ => m.volatility p.1 p.2 := by
  simp only [vol_eq m]
  exact (continuous_apply 0).comp (m.augmentedVolatility_continuous.comp cont_pair)

end ModelFacts

lemma interval_shift (g : ℝ → ℝ) (t0 s' : ℝ) (hs : 0 ≤ s') :
    ∫ r in t0..t0 + s', g r = ∫ r in Set.Ioc (0 : ℝ) s', g (t0 + r) := by
  have := intervalIntegral.integral_comp_add_left g t0 (a := 0) (b := s')
  rw [add_zero] at this
  rw [← this, intervalIntegral.integral_of_le hs]

lemma interval_shift2 (g : ℝ → ℝ) (t0 T : ℝ) (h : t0 ≤ T) :
    ∫ r in t0..T, g r = ∫ r in Set.Icc (0 : ℝ) (T - t0), g (t0 + r) := by
  have := interval_shift g t0 (T - t0) (sub_nonneg.2 h)
  rw [add_sub_cancel] at this
  rw [this, integral_Icc_eq_integral_Ioc]

lemma nn_sq (x : ℝ) : (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg x), ← Real.norm_eq_abs, ofReal_norm]
  rfl

/-- Mean zero of the Brownian stochastic integral at nonnegative times. -/
lemma si_mean_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω ∂P = 0 := by
  have hmart := martingale_stochasticIntegralBrownian W ℱ hℱ H hm hp hq
  have h1 := hmart.condExp_ae_eq ht
  have h0 := stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H hm hp hq (le_refl (0 : ℝ))
  rw [← integral_condExp (ℱ.le 0), integral_congr_ae (h1.trans h0)]
  simp

section Disc
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable def gV (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) (r : ℝ) : ℝ :=
  m.potential (m.augmentedPath r ω 0) (m.initialTime + r)

noncomputable def Acc (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..(max τ 0), gV m ω r

noncomputable def Dsc (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(Acc m τ ω))

lemma pot_cont (m : FeynmanKac.BoundedDiffusionModel P) :
    Continuous (Function.uncurry fun s x => m.potential x (m.initialTime + s)) := by
  have hpp : Continuous fun p : ℝ × ℝ => ((p.2, m.initialTime + p.1) : ℝ × ℝ) := by fun_prop
  exact m.potential_continuous.comp hpp

lemma gV_cont (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) : Continuous (gV m ω) := by
  obtain ⟨_, _, _, hX⟩ := m.isDiffusion
  have hc : Continuous fun r : ℝ => ((r, m.augmentedPath r ω 0) : ℝ × ℝ) :=
    continuous_id.prodMk ((continuous_apply 0).comp (hX.continuous_path ω))
  exact (pot_cont m).comp hc

lemma gV_prog (m : FeynmanKac.BoundedDiffusionModel P) :
    Probability.ProgressivelyMeasurable m.filtration (gV m) := by
  obtain ⟨_, _, _, hX⟩ := m.isDiffusion
  exact prog_time hX.continuous_path (fun t => (hX.adapted t).measurable) (pot_cont m)

lemma pot_bdd (m : FeynmanKac.BoundedDiffusionModel P) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x t, |m.potential x t| ≤ B := by
  obtain ⟨B, hB⟩ := m.potential_bounded
  exact ⟨max B 0, le_max_right _ _, fun x t => (hB x t).trans (le_max_left _ _)⟩

lemma Acc_nonneg (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : 0 ≤ Acc m τ ω :=
  intervalIntegral.integral_nonneg (le_max_right _ _) fun r _ => m.potential_nonneg _ _

lemma Dsc_pos (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : 0 < Dsc m τ ω :=
  Real.exp_pos _

lemma Dsc_le_one (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : Dsc m τ ω ≤ 1 :=
  Real.exp_le_one_iff.2 (neg_nonpos.2 (Acc_nonneg m τ ω))

lemma Dsc_abs_le (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (ω : Ω) : |Dsc m τ ω| ≤ 1 := by
  rw [abs_of_pos (Dsc_pos m τ ω)]; exact Dsc_le_one m τ ω

lemma Acc_cont (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) :
    Continuous fun τ => Acc m τ ω :=
  (intervalIntegral.continuous_primitive (fun a b => (gV_cont m ω).intervalIntegrable a b) 0).comp
    (continuous_id.max continuous_const)

lemma Dsc_cont (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) :
    Continuous fun τ => Dsc m τ ω :=
  Real.continuous_exp.comp (Acc_cont m ω).neg

lemma Dsc_zero (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) : Dsc m 0 ω = 1 := by
  simp [Dsc, Acc]

lemma Acc_meas (m : FeynmanKac.BoundedDiffusionModel P) (t : ℝ) :
    Measurable[m.filtration t] (Acc m t) := by
  by_cases ht : 0 ≤ t
  · have : Acc m t = fun ω => ∫ s in Set.Ioc (0 : ℝ) t, gV m ω s := by
      funext ω; simp [Acc, max_eq_left ht, intervalIntegral.integral_of_le ht]
    rw [this]
    exact ((gV_prog m).stronglyMeasurable_setIntegral measurableSet_Ioc
      (fun s hs => hs.2) volume).measurable
  · have : Acc m t = fun _ => 0 := by
      funext ω; simp [Acc, max_eq_right (not_le.1 ht).le]
    rw [this]; exact measurable_const

lemma Dsc_meas (m : FeynmanKac.BoundedDiffusionModel P) (t : ℝ) :
    Measurable[m.filtration t] (Dsc m t) :=
  (Acc_meas m t).neg.exp

lemma pd_eq (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) {r : ℝ} (hr : 0 ≤ r) :
    FeynmanKac.pathDiscount m.path m.potential m.initialTime (m.initialTime + r) ω =
      Dsc m r ω := by
  simp only [FeynmanKac.pathDiscount, Dsc, Acc, max_eq_left hr]
  congr 2
  have := intervalIntegral.integral_comp_add_left (fun q => m.potential (m.path q ω) q)
    m.initialTime (a := 0) (b := r)
  rw [add_zero] at this
  rw [← this]
  simp [gV, FeynmanKac.BoundedDiffusionModel.path]


lemma Dsc_prog (m : FeynmanKac.BoundedDiffusionModel P) :
    Probability.ProgressivelyMeasurable m.filtration (fun ω τ => Dsc m τ ω) := by
  apply Probability.ProgressivelyMeasurable.of_isStronglyProgressive
  exact StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (Dsc_meas m t).stronglyMeasurable) (fun ω => Dsc_cont m ω)

lemma Dsc_jm (m : FeynmanKac.BoundedDiffusionModel P) :
    Measurable (Function.uncurry fun ω τ => Dsc m τ ω) :=
  (measurable_uncurry_of_continuous_of_measurable (Dsc_cont m)
    (fun t => (Dsc_meas m t).mono (m.filtration.le t) le_rfl)).comp measurable_swap

end Disc

set_option maxHeartbeats 1600000 in
lemma adm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    m.AdmissibleDiscountedGradient u := by
  obtain ⟨⟨h1, h2, h3, c0, ct, cx, cxx⟩, -, -, -⟩ := hu
  set t0 := m.initialTime with ht0
  set T := m.terminalTime with hT
  have hTt : t0 ≤ T := m.horizon_nonneg
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hYc : ∀ ω, Continuous fun t => m.augmentedPath t ω := hX.continuous_path
  have hYa : ∀ t, Measurable[m.filtration t] (m.augmentedPath t) := fun t =>
    (hX.adapted t).measurable
  have hYm : ∀ t, Measurable (m.augmentedPath t) := fun t =>
    (hYa t).mono (m.filtration.le t) le_rfl
  let g : ℝ → ℝ → ℝ := fun τ x => m.volatility x (t0 + τ) * deriv (fun y => u y (t0 + τ)) x
  have hg : Continuous (Function.uncurry g) := by
    have hpp : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
    exact ((vol_cont m).comp hpp).mul (cx.comp hpp)
  let c : ℝ → ℝ := (Set.Icc (0 : ℝ) (T - t0)).indicator (fun _ => (1 : ℝ))
  have hc : Measurable c := measurable_const.indicator measurableSet_Icc
  let H : Ω → ℝ → ℝ := fun ω τ => Dsc m τ ω * (c τ * g τ (m.augmentedPath τ ω 0))
  have hH : m.discountedGradientIntegrand u = H := by
    funext ω τ
    simp only [FeynmanKac.BoundedDiffusionModel.discountedGradientIntegrand,
      FeynmanKac.BoundedDiffusionModel.spaceGradientIntegrand, H, c, g, Set.indicator_apply]
    split_ifs with hτ
    · rw [FeynmanKac.BoundedDiffusionModel.pathDiscount, ← ht0, pd_eq m ω hτ.1]
      simp [FeynmanKac.BoundedDiffusionModel.path, ← ht0]
    · simp
  unfold FeynmanKac.BoundedDiffusionModel.AdmissibleDiscountedGradient
  rw [hH]
  have hm : Measurable (Function.uncurry H) :=
    (Dsc_jm m).mul ((hc.comp measurable_snd).mul (meas_time hYc hYm hg))
  have hp : LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration H :=
    (Dsc_prog m).mul ((prog_det hc).mul (prog_time hYc hYa hg))
  refine ⟨hm, hp, ?_⟩
  intro T' _
  have hF : ∀ ω, ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 ≤
      ENNReal.ofReal (∫ s in t0..T, (m.pathDiscount s ω * m.volatility (m.path s ω) s *
        deriv (fun x => u x s) (m.path s ω)) ^ 2) := by
    intro ω
    have hcont : Continuous fun τ => Dsc m τ ω * g τ (m.augmentedPath τ ω 0) :=
      (Dsc_cont m ω).mul (hg.comp (continuous_id.prodMk ((continuous_apply 0).comp (hYc ω))))
    have hsupp : (fun τ => (‖H ω τ‖₊ : ℝ≥0∞) ^ 2).support ⊆ Set.Icc 0 (T - t0) := by
      intro τ hτ
      by_contra hn
      apply hτ
      simp [H, c, Set.indicator_of_notMem hn]
    calc ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2
        ≤ ∫⁻ τ, (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 := setLIntegral_le_lintegral _ _
      _ = ∫⁻ τ in Set.Icc 0 (T - t0), (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 :=
          (setLIntegral_eq_of_support_subset hsupp).symm
      _ = ∫⁻ τ in Set.Icc 0 (T - t0),
            ENNReal.ofReal ((Dsc m τ ω * g τ (m.augmentedPath τ ω 0)) ^ 2) :=
          setLIntegral_congr_fun measurableSet_Icc (fun τ hτ => by
            rw [← nn_sq]; simp [H, c, Set.indicator_of_mem hτ])
      _ = ENNReal.ofReal (∫ τ in Set.Icc 0 (T - t0),
            (Dsc m τ ω * g τ (m.augmentedPath τ ω 0)) ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal ((hcont.pow 2).integrableOn_Icc)
            (ae_of_all _ fun _ => sq_nonneg _)).symm
      _ = _ := by
          congr 1
          rw [interval_shift2 _ _ _ hTt]
          refine setIntegral_congr_fun measurableSet_Icc (fun τ hτ => ?_)
          have hpd := pd_eq m ω hτ.1
          rw [← ht0] at hpd
          simp only [g, FeynmanKac.BoundedDiffusionModel.pathDiscount, ← ht0, hpd,
            FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left]
          ring
  calc ∫⁻ ω, ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (∫ s in t0..T, (m.pathDiscount s ω *
          m.volatility (m.path s ω) s * deriv (fun x => u x s) (m.path s ω)) ^ 2) ∂P :=
        lintegral_mono hF
    _ < ⊤ := hgrad.2.lintegral_lt_top

lemma dr_meas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ)
    (c0 : Continuous fun z : ℝ × ℝ => u z.1 z.2) {c : ℝ} (hc : 0 ≤ c) :
    StronglyMeasurable[m.filtration c]
      (fun ω => m.discountedReward u (m.initialTime + c) ω) := by
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hYc : ∀ ω, Continuous fun t => m.augmentedPath t ω := hX.continuous_path
  have hYa : ∀ t, Measurable[m.filtration t] (m.augmentedPath t) := fun t =>
    (hX.adapted t).measurable
  have hf : Continuous (Function.uncurry fun τ x => m.runningSource x (m.initialTime + τ)) := by
    have hpp : Continuous fun p : ℝ × ℝ => ((p.2, m.initialTime + p.1) : ℝ × ℝ) := by fun_prop
    exact m.source_continuous.comp hpp
  have heq : (fun ω => m.discountedReward u (m.initialTime + c) ω) = fun ω =>
      Dsc m c ω * u (m.augmentedPath c ω 0) (m.initialTime + c) +
        ∫ τ in Set.Ioc (0 : ℝ) c, Dsc m τ ω * m.runningSource (m.augmentedPath τ ω 0)
          (m.initialTime + τ) := by
    funext ω
    simp only [FeynmanKac.BoundedDiffusionModel.discountedReward, FeynmanKac.discountedReward]
    rw [pd_eq m ω hc, interval_shift _ _ _ hc]
    congr 1
    · simp [FeynmanKac.BoundedDiffusionModel.path]
    · refine setIntegral_congr_fun measurableSet_Ioc (fun τ hτ => ?_)
      rw [pd_eq m ω hτ.1.le]
      simp [FeynmanKac.BoundedDiffusionModel.path]
  rw [heq]
  refine StronglyMeasurable.add ?_ ?_
  · refine Measurable.stronglyMeasurable ?_
    refine (Dsc_meas m c).mul ?_
    have hcu : Continuous fun y : Fin 2 → ℝ => u (y 0) (m.initialTime + c) :=
      c0.comp (by fun_prop : Continuous fun y : Fin 2 → ℝ => ((y 0, m.initialTime + c) : ℝ × ℝ))
    exact hcu.measurable.comp (hYa c)
  · exact ((Dsc_prog m).mul (prog_time hYc hYa hf)).stronglyMeasurable_setIntegral
      measurableSet_Ioc (fun s hs => hs.2) volume

end S87K

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u)
    (hdisc : m.AdmissibleDiscountedGradient u) :
    MeasureTheory.Martingale
      (fun r ω => m.discountedReward u
        (m.initialTime + min (max r 0) (m.terminalTime - m.initialTime)) ω)
      ⟨fun r => m.filtration (max r 0),
        fun _ _ h => m.filtration.mono (max_le_max h (le_refl (0 : ℝ))),
        fun r => m.filtration.le (max r 0)⟩ P := by
  open MeasureTheory in
  have hmart := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegralBrownian
    (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (m.discountedGradientIntegrand u) hdisc.1 hdisc.2.1 hdisc.2.2
  set SI := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
    (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (m.discountedGradientIntegrand u) hdisc.1 hdisc.2.1 hdisc.2.2 with hSI
  have hTt : 0 ≤ m.terminalTime - m.initialTime := sub_nonneg.2 m.horizon_nonneg
  have hk0 : ∀ r, 0 ≤ min (max r 0) (m.terminalTime - m.initialTime) := fun r =>
    le_min (le_max_right _ _) hTt
  have hae : ∀ r, (fun ω => m.discountedReward u
        (m.initialTime + min (max r 0) (m.terminalTime - m.initialTime)) ω) =ᵐ[P]
      (fun ω => u m.initialState m.initialTime +
        SI (min (max r 0) (m.terminalTime - m.initialTime)) ω) := by
    intro r
    have hs : m.initialTime + min (max r 0) (m.terminalTime - m.initialTime) ∈
        Set.Icc m.initialTime m.terminalTime :=
      ⟨by linarith [hk0 r], by linarith [min_le_right (max r 0) (m.terminalTime - m.initialTime)]⟩
    have := FeynmanKac.discounted_reward_ito_identity P m u hu hdisc _ hs
    simpa only [FeynmanKac.BoundedDiffusionModel.discountedGradientItoIntegral,
      add_sub_cancel_left] using this
  refine ⟨fun r => ?_, fun i j hij => ?_⟩
  · exact (S87K.dr_meas m u hu.1.2.2.2.1 (hk0 r)).mono
      (m.filtration.mono (min_le_left _ _))
  · show P[_ | m.filtration (max i 0)] =ᵐ[P] _
    have hint : ∀ c, MeasureTheory.Integrable (SI c) P := fun c => hmart.integrable c
    have hle : min (max i 0) (m.terminalTime - m.initialTime) ≤
        min (max j 0) (m.terminalTime - m.initialTime) :=
      min_le_min (max_le_max hij le_rfl) le_rfl
    have key : P[SI (min (max j 0) (m.terminalTime - m.initialTime)) | m.filtration (max i 0)]
        =ᵐ[P] SI (min (max i 0) (m.terminalTime - m.initialTime)) := by
      by_cases h : min (max i 0) (m.terminalTime - m.initialTime) = max i 0
      · rw [h] at hle ⊢
        exact hmart.condExp_ae_eq hle
      · have h1 : min (max i 0) (m.terminalTime - m.initialTime) =
            m.terminalTime - m.initialTime := by
          rcases min_choice (max i 0) (m.terminalTime - m.initialTime) with h' | h'
          · exact absurd h' h
          · exact h'
        have h2 : min (max j 0) (m.terminalTime - m.initialTime) =
            m.terminalTime - m.initialTime :=
          le_antisymm (min_le_right _ _) (by rw [h1] at hle; exact hle)
        have h3 : m.terminalTime - m.initialTime ≤ max i 0 := by
          rw [← h1]; exact min_le_left _ _
        rw [h1, h2]
        refine (MeasureTheory.condExp_of_stronglyMeasurable (m.filtration.le _)
          ((hmart.1 _).mono (m.filtration.mono h3)) (hint _)).eventuallyEq
    have e1 := MeasureTheory.condExp_congr_ae (m := m.filtration (max i 0)) (hae j)
    have e2 := MeasureTheory.condExp_add (MeasureTheory.integrable_const
      (u m.initialState m.initialTime)) (hint (min (max j 0) (m.terminalTime - m.initialTime)))
      (m.filtration (max i 0)) (μ := P)
    rw [MeasureTheory.condExp_const (m.filtration.le _)] at e2
    refine e1.trans (e2.trans ?_)
    filter_upwards [key, hae i] with ω hk hi
    simp only [Pi.add_apply] at hk ⊢
    rw [hk, hi]
