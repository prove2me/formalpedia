-- Prove2me | solution 1 for FeynmanKac.heat_terminal_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:23:28.27225+00:00
-- url     : https://prove2.me/submissions/8b91a4a8-9d65-40f2-ba15-1c98ee946207

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
import Theorems.Thm_FeynmanKac_space_time_ito_formula
import Mathlib

namespace S87G

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal

/-! ### Progressive measurability with explicit time dependence -/

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

/-! ### The discounted function -/

noncomputable def disc (r t0 : ℝ) (u : ℝ → ℝ → ℝ) (x s : ℝ) : ℝ :=
  Real.exp (-(r * (s - t0))) * u x s

lemma e_hasDeriv (r t0 s : ℝ) :
    HasDerivAt (fun s => Real.exp (-(r * (s - t0)))) (Real.exp (-(r * (s - t0))) * (-r)) s := by
  have h : HasDerivAt (fun s => -(r * (s - t0))) (-r) s := by
    have h0 : HasDerivAt (fun s => r * (s - t0)) (r * 1) s :=
      ((hasDerivAt_id' s).sub_const t0).const_mul r
    have h1 := h0.neg
    rw [mul_one] at h1
    exact h1
  exact h.exp

lemma e_cont (r t0 : ℝ) : Continuous fun s : ℝ => Real.exp (-(r * (s - t0))) := by fun_prop

lemma disc_dx (r t0 : ℝ) (u : ℝ → ℝ → ℝ) (s : ℝ) :
    deriv (fun x => disc r t0 u x s) =
      fun x => Real.exp (-(r * (s - t0))) * deriv (fun x => u x s) x := by
  unfold disc
  exact deriv_const_mul_field' _

lemma disc_dxx (r t0 : ℝ) (u : ℝ → ℝ → ℝ) (s x : ℝ) :
    deriv (deriv (fun x => disc r t0 u x s)) x =
      Real.exp (-(r * (s - t0))) * deriv (deriv (fun x => u x s)) x := by
  rw [disc_dx, deriv_const_mul_field']

lemma disc_dt (r t0 : ℝ) (u : ℝ → ℝ → ℝ) (h2 : ∀ x, Differentiable ℝ (fun s => u x s))
    (x s : ℝ) :
    deriv (fun q => disc r t0 u x q) s =
      Real.exp (-(r * (s - t0))) * (-r) * u x s +
        Real.exp (-(r * (s - t0))) * deriv (fun q => u x q) s := by
  unfold disc
  exact ((e_hasDeriv r t0 s).mul ((h2 x) s).hasDerivAt).deriv

lemma disc_isC12 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) (r t0 : ℝ) (u : ℝ → ℝ → ℝ) (hu : m.IsC12 u) :
    m.IsC12 (disc r t0 u) := by
  obtain ⟨h1, h2, h3, c0, ct, cx, cxx⟩ := hu
  have ce := e_cont r t0
  have ces : Continuous fun z : ℝ × ℝ => Real.exp (-(r * (z.2 - t0))) := ce.comp continuous_snd
  refine ⟨fun s => ?_, fun x => ?_, fun s => ?_, ?_, ?_, ?_, ?_⟩
  · exact (h1 s).const_mul _
  · exact Differentiable.mul (fun s => (e_hasDeriv r t0 s).differentiableAt) (h2 x)
  · rw [disc_dx]; exact (h3 s).const_mul _
  · exact ces.mul c0
  · have : (fun z : ℝ × ℝ => deriv (fun s => disc r t0 u z.1 s) z.2) =
        fun z => Real.exp (-(r * (z.2 - t0))) * (-r) * u z.1 z.2 +
          Real.exp (-(r * (z.2 - t0))) * deriv (fun q => u z.1 q) z.2 := by
      funext z; exact disc_dt r t0 u h2 z.1 z.2
    rw [this]
    exact ((ces.mul continuous_const).mul c0).add (ces.mul ct)
  · have : (fun z : ℝ × ℝ => deriv (fun x => disc r t0 u x z.2) z.1) =
        fun z => Real.exp (-(r * (z.2 - t0))) * deriv (fun x => u x z.2) z.1 := by
      funext z; rw [disc_dx]
    rw [this]
    exact ces.mul cx
  · have : (fun z : ℝ × ℝ => deriv (deriv (fun x => disc r t0 u x z.2)) z.1) =
        fun z => Real.exp (-(r * (z.2 - t0))) * deriv (deriv (fun x => u x z.2)) z.1 := by
      funext z; rw [disc_dxx]
    rw [this]
    exact ces.mul cxx

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

set_option maxHeartbeats 1600000 in
theorem main
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (r : ℝ) (hr : 0 ≤ r) (hV : ∀ x s, m.potential x s = r)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, (Real.exp (-(r * (m.terminalTime - m.initialTime))) *
          m.terminalPayoff (m.path m.terminalTime ω) +
        ∫ s in m.initialTime..m.terminalTime,
          Real.exp (-(r * (s - m.initialTime))) *
            m.runningSource (m.path s ω) s) ∂P := by
  obtain ⟨hC12, -, hterm, hpde⟩ := hu
  obtain ⟨h1, h2, h3, c0, ct, cx, cxx⟩ := hC12
  set t0 := m.initialTime with ht0
  set T := m.terminalTime with hT
  have hTt : t0 ≤ T := m.horizon_nonneg
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hYc : ∀ ω, Continuous fun t => m.augmentedPath t ω := hX.continuous_path
  have hYa : ∀ t, Measurable[m.filtration t] (m.augmentedPath t) := fun t =>
    (hX.adapted t).measurable
  have hYm : ∀ t, Measurable (m.augmentedPath t) := fun t =>
    (hYa t).mono (m.filtration.le t) le_rfl
  -- the integrand
  let g : ℝ → ℝ → ℝ := fun τ x => m.volatility x (t0 + τ) *
    (Real.exp (-(r * (t0 + τ - t0))) * deriv (fun y => u y (t0 + τ)) x)
  have hg : Continuous (Function.uncurry g) := by
    have hpp : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
    have hpq : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
    exact ((vol_cont m).comp hpp).mul
      (((e_cont r t0).comp (continuous_const.add continuous_fst)).mul (cx.comp hpq))
  let c : ℝ → ℝ := (Set.Icc (0 : ℝ) (T - t0)).indicator (fun _ => (1 : ℝ))
  have hc : Measurable c := measurable_const.indicator measurableSet_Icc
  let H : Ω → ℝ → ℝ := fun ω τ => c τ * g τ (m.augmentedPath τ ω 0)
  have hH : ∀ (ω : Ω) (τ : ℝ),
      H ω τ =
        if τ ∈ Set.Icc (0 : ℝ) (T - t0) then
          m.volatility (m.path (t0 + τ) ω) (t0 + τ) *
            deriv (fun x => disc r t0 u x (t0 + τ)) (m.path (t0 + τ) ω)
        else 0 := by
    intro ω τ
    rw [disc_dx]
    simp only [H, c, g, Set.indicator_apply, FeynmanKac.BoundedDiffusionModel.path, ← ht0,
      add_sub_cancel_left]
    split_ifs <;> simp
  have hm : Measurable (Function.uncurry H) :=
    (hc.comp measurable_snd).mul (meas_time hYc hYm hg)
  have hp : LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration H :=
    LevyStochCalc.Probability.ProgressivelyMeasurable.mul (prog_det hc) (prog_time hYc hYa hg)
  have hq : ∀ (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ τ in Set.Icc (0 : ℝ) T',
        (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤ := by
    intro T' _
    have hF : ∀ ω, ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (∫ s in t0..T, (m.pathDiscount s ω * m.volatility (m.path s ω) s *
          deriv (fun x => u x s) (m.path s ω)) ^ 2) := by
      intro ω
      have hcont : Continuous fun τ => g τ (m.augmentedPath τ ω 0) :=
        hg.comp (continuous_id.prodMk ((continuous_apply 0).comp (hYc ω)))
      have hsupp : (fun τ => (‖H ω τ‖₊ : ℝ≥0∞) ^ 2).support ⊆ Set.Icc 0 (T - t0) := by
        intro τ hτ
        by_contra hn
        apply hτ
        simp [H, c, Set.indicator_of_notMem hn]
      calc ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2
          ≤ ∫⁻ τ, (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 := setLIntegral_le_lintegral _ _
        _ = ∫⁻ τ in Set.Icc 0 (T - t0), (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 :=
            (setLIntegral_eq_of_support_subset hsupp).symm
        _ = ∫⁻ τ in Set.Icc 0 (T - t0), ENNReal.ofReal ((g τ (m.augmentedPath τ ω 0)) ^ 2) :=
            setLIntegral_congr_fun measurableSet_Icc (fun τ hτ => by
              rw [← nn_sq]; simp [H, c, Set.indicator_of_mem hτ])
        _ = ENNReal.ofReal (∫ τ in Set.Icc 0 (T - t0), (g τ (m.augmentedPath τ ω 0)) ^ 2) :=
            (ofReal_integral_eq_lintegral_ofReal ((hcont.pow 2).integrableOn_Icc)
              (ae_of_all _ fun _ => sq_nonneg _)).symm
        _ = _ := by
            congr 1
            rw [interval_shift2 _ _ _ hTt]
            refine integral_congr_ae (ae_of_all _ fun τ => ?_)
            simp only [g, FeynmanKac.BoundedDiffusionModel.pathDiscount, FeynmanKac.pathDiscount,
              hV, intervalIntegral.integral_const, smul_eq_mul,
              FeynmanKac.BoundedDiffusionModel.path, ← ht0, add_sub_cancel_left]
            ring_nf
    calc ∫⁻ ω, ∫⁻ τ in Set.Icc (0 : ℝ) T', (‖H ω τ‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (∫ s in t0..T, (m.pathDiscount s ω *
            m.volatility (m.path s ω) s * deriv (fun x => u x s) (m.path s ω)) ^ 2) ∂P :=
          lintegral_mono hF
      _ < ⊤ := hgrad.2.lintegral_lt_top
  have ito := FeynmanKac.space_time_ito_formula P m (disc r t0 u)
    (disc_isC12 m r t0 u ⟨h1, h2, h3, c0, ct, cx, cxx⟩) H hH hm hp hq T ⟨hTt, le_rfl⟩
  have hae : (fun ω => Real.exp (-(r * (T - t0))) * m.terminalPayoff (m.path T ω) +
        ∫ s in t0..T, Real.exp (-(r * (s - t0))) * m.runningSource (m.path s ω) s) =ᵐ[P]
      (fun ω => u m.initialState t0 + stochasticIntegralBrownian
          (m.brownian.W 0) m.filtration (m.brownianFiltration 0) H hm hp hq (T - t0) ω) := by
    filter_upwards [ito] with ω hω
    have hD : (∫ τ in t0..T,
        deriv (fun q => disc r t0 u (m.path τ ω) q) τ +
          m.drift (m.path τ ω) τ * deriv (fun x => disc r t0 u x τ) (m.path τ ω) +
          (1 / 2 : ℝ) * (m.volatility (m.path τ ω) τ) ^ 2 *
            deriv (deriv (fun x => disc r t0 u x τ)) (m.path τ ω)) =
        ∫ τ in t0..T, -(Real.exp (-(r * (τ - t0))) * m.runningSource (m.path τ ω) τ) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le hTt] at hτ
      have e := hpde (m.path τ ω) τ hτ
      rw [hV] at e
      rw [disc_dt r t0 u h2, disc_dxx, disc_dx]
      linear_combination (Real.exp (-(r * (τ - t0)))) * e
    rw [← ht0, hD, intervalIntegral.integral_neg] at hω
    simp only [disc, sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul, hterm] at hω
    linarith
  rw [integral_congr_ae hae, integral_add (integrable_const _)
    ((martingale_stochasticIntegralBrownian _ _ _ H hm hp hq).integrable _),
    si_mean_zero _ _ _ H hm hp hq (sub_nonneg.2 hTt)]
  simp

end S87G

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsClassicalPDESolution u)
    (hμ : ∀ x s, m.drift x s = 0)
    (hσ : ∀ x s, m.volatility x s = 1)
    (hV : ∀ x s, m.potential x s = 0)
    (hf : ∀ x s, m.runningSource x s = 0)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, m.terminalPayoff (m.path m.terminalTime ω) ∂P := by
  rw [S87G.main P m 0 le_rfl hV u hu hgrad]
  simp [hf]
