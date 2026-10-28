-- Prove2me | solution 1 for FeynmanKac.discounted_reward_ito_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:45:27.746804+00:00
-- url     : https://prove2.me/submissions/6356acc3-1a51-4332-815f-ac66bac3e6da

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionQuadVar
import Definitions.Def_KLSModular_LevyStochCalc_Probability_ExitTime
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
import Theorems.Thm_ItoLemma_ito_formula_time_dependent_bounded
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_congr_of_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_sub_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_ae_zero_readable
import Theorems.Thm_LevyStochCalc_Probability_exitTime_le_iff_readable
import Theorems.Thm_LevyStochCalc_Probability_norm_le_of_le_exitTime_readable
import Theorems.Thm_LevyStochCalc_Probability_exists_lt_exitTime_readable
import Theorems.Thm_ItoLemma_continuous_adapted_composition_progressive
import Definitions.Def_FeynmanKac_AdmissibleDiscountedGradient
import Definitions.Def_FeynmanKac_ModelReward
import Theorems.Thm_ItoCalculusII_continuous_product_rule_bounded_state
import Mathlib

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal

namespace S87H

/-! ### Cutoffs -/

lemma cutoff (a b : ℝ) : ∃ χ : ℝ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧
    ∀ x ∈ Set.Ioo (a - 1) (b + 1), χ x = 1 := by
  let f : ContDiffBump ((a + b) / 2) :=
    ⟨|b - a| + 1, |b - a| + 2, by positivity, by linarith⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, fun x hx => ?_⟩
  apply f.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  have := le_abs_self (b - a)
  have := neg_abs_le (b - a)
  obtain ⟨h1, h2⟩ := hx
  show _ ∧ _ ≤ |b - a| + 1
  constructor <;> linarith

lemma deriv_zero_of_eq_one {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ x ∈ U, χ x = 1) {x : ℝ} (hx : x ∈ U) : deriv χ x = 0 := by
  have : χ =ᶠ[nhds x] fun _ => (1 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) h
  rw [this.deriv_eq]; simp

lemma deriv2_zero_of_eq_one {χ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (h : ∀ x ∈ U, χ x = 1) {x : ℝ} (hx : x ∈ U) : deriv (deriv χ) x = 0 := by
  have : deriv χ =ᶠ[nhds x] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => deriv_zero_of_eq_one hU h hy
  rw [this.deriv_eq]; simp

/-! ### Stochastic integral congruences -/

section SI
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

lemma si_congr_eq {H₁ H₂ : Ω → ℝ → ℝ} (h : H₁ = H₂)
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t =
      stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  subst h; rfl

lemma prog_sub {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {A B : Ω → ℝ → ℝ} (hA : Probability.ProgressivelyMeasurable ℱ A)
    (hB : Probability.ProgressivelyMeasurable ℱ B) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => A ω s - B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s - B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 - (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, sub_zero]
  rw [key]
  exact (hA t).sub (hB t)

lemma si_ae_zero_of_ae {D : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry D))
    (hp : Probability.ProgressivelyMeasurable ℱ D)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (h : ∀ᵐ ω ∂P, ∀ r, 0 < r → r ≤ t → D ω r = 0) :
    stochasticIntegralBrownian W ℱ hℱ D hm hp hq t =ᵐ[P] 0 := by
  have hiso := isometry_stochasticIntegralBrownian W ℱ hℱ D hm hp hq ht
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))]
    · simp
    filter_upwards [h] with ω hω
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
    rw [setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞))
      (fun r hr => by simp [hω r hr.1 hr.2])]
    simp
  rw [hzero] at hiso
  have hmeas := (stochasticIntegralBrownian_memLp W ℱ hℱ D hm hp hq t).aestronglyMeasurable
  have hae := (lintegral_eq_zero_iff'
    ((hmeas.aemeasurable.nnnorm.coe_nnreal_ennreal).pow_const 2)).1 hiso
  filter_upwards [hae] with ω hω
  simpa using hω

lemma si_congr_ae {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (h : ∀ᵐ ω ∂P, ∀ r, 0 < r → r ≤ t → H₁ ω r = H₂ ω r) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t =ᵐ[P]
      stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t := by
  have hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s) := hm₁.sub hm₂
  have hps := prog_sub hp₁ hp₂
  have h1 := stochasticIntegralBrownian_sub_readable W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hms hps hqs ht
  have h2 := si_ae_zero_of_ae W ℱ hℱ hms hps hqs ht (by
    filter_upwards [h] with ω hω r hr hrt
    simp [hω r hr hrt])
  filter_upwards [h1, h2] with ω e1 e2
  rw [e2] at e1
  simp only [Pi.zero_apply] at e1
  linarith

end SI

/-! ### Exit time is a stopping time -/

lemma exit_isStoppingTime {Ω : Type*} [MeasurableSpace Ω] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (X : Ω → ℝ → ℝ) (hc : ∀ ω, Continuous (X ω)) (ha : ∀ t, Measurable[ℱ t] (fun ω => X ω t))
    (R : ℝ) : IsStoppingTime ℱ (Probability.exitTime X R) := by
  intro t
  by_cases ht : 0 ≤ t
  · have key : {ω | Probability.exitTime X R ω ≤ t} =
        (⋃ n : ℕ, ⋂ q : ℚ, {ω | ‖X ω (max 0 (min t (q : ℝ)))‖ ≤ R - 1 / ((n : ℝ) + 1)})ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter]
      rw [Probability.exitTime_le_iff_readable (hc ω)]
      have hcl : Continuous fun r : ℝ => ‖X ω (max 0 (min t r))‖ :=
        ((hc ω).comp (continuous_const.max (continuous_const.min continuous_id))).norm
      constructor
      · rintro ⟨s, hs, hRs⟩ ⟨n, hn⟩
        have hall : ∀ r : ℝ, ‖X ω (max 0 (min t r))‖ ≤ R - 1 / ((n : ℝ) + 1) := fun r =>
          Rat.denseRange_cast.induction_on (p := fun r => ‖X ω (max 0 (min t r))‖ ≤
            R - 1 / ((n : ℝ) + 1)) r (isClosed_le hcl continuous_const) hn
        have h1 := hall s
        rw [min_eq_right hs.2, max_eq_right hs.1] at h1
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro h
        by_contra hne
        push_neg at hne
        obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
          (Set.nonempty_Icc.2 ht) ((hc ω).norm.continuousOn (s := Set.Icc 0 t))
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (hne s₀ hs₀))
        refine h ⟨n, fun q => ?_⟩
        have hm : max 0 (min t (q : ℝ)) ∈ Set.Icc 0 t :=
          ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
        have := hmax hm
        simp only [Set.mem_setOf_eq] at this
        linarith
    rw [key]
    refine MeasurableSet.compl (m := ℱ t) (MeasurableSet.iUnion (m := ℱ t) fun n =>
      MeasurableSet.iInter (m := ℱ t) fun q => ?_)
    have hq : Measurable[ℱ t] (fun ω => X ω (max 0 (min t (q : ℝ)))) :=
      (ha _).mono (ℱ.mono (max_le ht (min_le_left _ _))) le_rfl
    exact (measurable_norm.comp hq) measurableSet_Iic
  · have key : {ω | Probability.exitTime X R ω ≤ t} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rw [Probability.exitTime_le_iff_readable (hc ω)]
      rintro ⟨s, hs, -⟩
      exact ht (hs.1.trans hs.2)
    rw [key]; exact @MeasurableSet.empty _ (ℱ t)

/-! ### The model -/

section Model
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma clock_pt (m : FeynmanKac.BoundedDiffusionModel P) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∀ᵐ ω ∂P, m.augmentedPath τ ω 1 = m.initialTime + τ := by
  obtain ⟨hm, hp, hq, hX⟩ := m.isDiffusion
  have hm0 := hm 1 0
  have hp0 := hp 1 0
  have hq0 := hq 1 0
  simp only [m.augmentedVolatility_clock] at hm0 hp0 hq0
  have hz := stochasticIntegralBrownian_ae_zero_readable (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) hm0 hp0 hq0 τ
  have hc := si_congr_eq (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (H₁ := fun ω s => m.augmentedVolatility (m.augmentedPath s ω) 0 1)
    (H₂ := fun _ _ => (0 : ℝ)) (by funext ω s; exact m.augmentedVolatility_clock _)
    (hm 1 0) (hp 1 0) (hq 1 0) hm0 hp0 hq0 τ
  filter_upwards [hX.ae_eq τ hτ, hz] with ω e1 e2
  rw [e1]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one]
  have e3 : stochasticIntegralBrownian (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
      (fun ω s => m.augmentedVolatility (m.augmentedPath s ω) 0 1) (hm 1 0) (hp 1 0) (hq 1 0)
      τ ω = 0 := by rw [hc]; exact e2
  rw [e3]
  simp [m.augmentedDrift_clock, m.initialCoordinates_clock, hτ]

lemma clock (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, ∀ τ, 0 ≤ τ → m.augmentedPath τ ω 1 = m.initialTime + τ := by
  obtain ⟨hm, hp, hq, hX⟩ := m.isDiffusion
  have h : ∀ᵐ ω ∂P, ∀ q : ℚ, m.augmentedPath (max (q : ℝ) 0) ω 1 =
      m.initialTime + max (q : ℝ) 0 :=
    ae_all_iff.2 fun q => clock_pt m _ (le_max_right _ _)
  filter_upwards [h] with ω hω τ hτ
  have hcont : Continuous fun r : ℝ => m.augmentedPath (max r 0) ω 1 :=
    (continuous_apply 1).comp ((hX.continuous_path ω).comp (continuous_id.max continuous_const))
  have := Rat.denseRange_cast.induction_on (p := fun r : ℝ =>
    m.augmentedPath (max r 0) ω 1 = m.initialTime + max r 0) τ
    (isClosed_eq hcont (continuous_const.add (continuous_id.max continuous_const))) hω
  simpa [max_eq_left hτ] using this

end Model

/-! ### The truncated test function -/

section Analytic
variable (u : ℝ → ℝ → ℝ) (φ χ : ℝ → ℝ) (t0 : ℝ)

noncomputable def ut (x s : ℝ) : ℝ := deriv (fun q => u x q) s
noncomputable def ux (x s : ℝ) : ℝ := deriv (fun y => u y s) x
noncomputable def uxx (x s : ℝ) : ℝ := deriv (deriv (fun y => u y s)) x

noncomputable def F (τ x : ℝ) : ℝ := φ τ * (χ x * u x (t0 + τ))
noncomputable def Ft (τ x : ℝ) : ℝ :=
  deriv φ τ * (χ x * u x (t0 + τ)) + φ τ * (χ x * ut u x (t0 + τ))
noncomputable def Fx (τ x : ℝ) : ℝ :=
  φ τ * (deriv χ x * u x (t0 + τ) + χ x * ux u x (t0 + τ))
noncomputable def Fxx (τ x : ℝ) : ℝ :=
  φ τ * ((deriv (deriv χ) x * u x (t0 + τ) + deriv χ x * ux u x (t0 + τ)) +
    (deriv χ x * ux u x (t0 + τ) + χ x * uxx u x (t0 + τ)))

variable {u φ χ}
variable (h1 : ∀ s, Differentiable ℝ (fun x => u x s))
  (h2 : ∀ x, Differentiable ℝ (fun s => u x s))
  (h3 : ∀ s, Differentiable ℝ (deriv (fun x => u x s)))
  (c0 : Continuous (fun z : ℝ × ℝ => u z.1 z.2))
  (ct : Continuous (fun z : ℝ × ℝ => deriv (fun s => u z.1 s) z.2))
  (cx : Continuous (fun z : ℝ × ℝ => deriv (fun x => u x z.2) z.1))
  (cxx : Continuous (fun z : ℝ × ℝ => deriv (deriv (fun x => u x z.2)) z.1))
  (hφ : ContDiff ℝ 2 φ) (hχ : ContDiff ℝ 2 χ)
  (sφ : HasCompactSupport φ) (sχ : HasCompactSupport χ)

include h2 hφ in
lemma hasDeriv_t (τ x : ℝ) : HasDerivAt (fun r => F u φ χ t0 r x) (Ft u φ χ t0 τ x) τ := by
  have hu : HasDerivAt (fun r => u x (t0 + r)) (ut u x (t0 + τ)) τ :=
    ((h2 x) (t0 + τ)).hasDerivAt.comp_const_add t0 τ
  have hp : HasDerivAt φ (deriv φ τ) τ :=
    ((hφ.differentiable (by norm_num)) τ).hasDerivAt
  exact hp.mul (hu.const_mul (χ x))

include h1 hχ in
lemma hasDeriv_x (τ x : ℝ) : HasDerivAt (fun y => F u φ χ t0 τ y) (Fx u φ χ t0 τ x) x := by
  have hu : HasDerivAt (fun y => u y (t0 + τ)) (ux u x (t0 + τ)) x :=
    ((h1 (t0 + τ)) x).hasDerivAt
  have hc : HasDerivAt χ (deriv χ x) x :=
    ((hχ.differentiable (by norm_num)) x).hasDerivAt
  exact (hc.mul hu).const_mul (φ τ)

include h1 h3 hχ in
lemma hasDeriv_xx (τ x : ℝ) : HasDerivAt (fun y => Fx u φ χ t0 τ y) (Fxx u φ χ t0 τ x) x := by
  have hu : HasDerivAt (fun y => u y (t0 + τ)) (ux u x (t0 + τ)) x :=
    ((h1 (t0 + τ)) x).hasDerivAt
  have hu' : HasDerivAt (fun y => ux u y (t0 + τ)) (uxx u x (t0 + τ)) x :=
    ((h3 (t0 + τ)) x).hasDerivAt
  have hc : HasDerivAt χ (deriv χ x) x :=
    ((hχ.differentiable (by norm_num)) x).hasDerivAt
  have hc1 : ContDiff ℝ 1 (deriv χ) := hχ.deriv'
  have hc' : HasDerivAt (deriv χ) (deriv (deriv χ) x) x :=
    ((hc1.differentiable (by norm_num)) x).hasDerivAt
  exact ((hc'.mul hu).add (hc.mul hu')).const_mul (φ τ)

include c0 ct hφ hχ in
lemma cont_t : Continuous (Function.uncurry (Ft u φ χ t0)) := by
  have g : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
  have cφ : Continuous fun p : ℝ × ℝ => φ p.1 := hφ.continuous.comp continuous_fst
  have cφ' : Continuous fun p : ℝ × ℝ => deriv φ p.1 := (hφ.continuous_deriv (by norm_num)).comp continuous_fst
  have cχ : Continuous fun p : ℝ × ℝ => χ p.2 := hχ.continuous.comp continuous_snd
  have cu := c0.comp g
  have cut := ct.comp g
  show Continuous fun p : ℝ × ℝ => Ft u φ χ t0 p.1 p.2
  unfold Ft ut
  exact (cφ'.mul (cχ.mul cu)).add (cφ.mul (cχ.mul cut))

include c0 cx hφ hχ in
lemma cont_x : Continuous (Function.uncurry (Fx u φ χ t0)) := by
  have g : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
  have cφ : Continuous fun p : ℝ × ℝ => φ p.1 := hφ.continuous.comp continuous_fst
  have cχ : Continuous fun p : ℝ × ℝ => χ p.2 := hχ.continuous.comp continuous_snd
  have cχ' : Continuous fun p : ℝ × ℝ => deriv χ p.2 := (hχ.continuous_deriv (by norm_num)).comp continuous_snd
  have cu := c0.comp g
  have cux := cx.comp g
  show Continuous fun p : ℝ × ℝ => Fx u φ χ t0 p.1 p.2
  unfold Fx ux
  exact cφ.mul ((cχ'.mul cu).add (cχ.mul cux))

include c0 cx cxx hφ hχ in
lemma cont_xx : Continuous (Function.uncurry (Fxx u φ χ t0)) := by
  have g : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
  have cφ : Continuous fun p : ℝ × ℝ => φ p.1 := hφ.continuous.comp continuous_fst
  have cχ : Continuous fun p : ℝ × ℝ => χ p.2 := hχ.continuous.comp continuous_snd
  have cχ' : Continuous fun p : ℝ × ℝ => deriv χ p.2 := (hχ.continuous_deriv (by norm_num)).comp continuous_snd
  have hc1 : ContDiff ℝ 1 (deriv χ) := hχ.deriv'
  have cχ'' : Continuous fun p : ℝ × ℝ => deriv (deriv χ) p.2 := (hc1.continuous_deriv le_rfl).comp continuous_snd
  have cu := c0.comp g
  have cux := cx.comp g
  have cuxx := cxx.comp g
  show Continuous fun p : ℝ × ℝ => Fxx u φ χ t0 p.1 p.2
  unfold Fxx ux uxx
  exact cφ.mul (((cχ''.mul cu).add (cχ'.mul cux)).add ((cχ'.mul cux).add (cχ.mul cuxx)))

lemma zero_off {p : ℝ × ℝ} (hp : p ∉ tsupport φ ×ˢ tsupport χ) :
    (φ p.1 = 0 ∧ deriv φ p.1 = 0) ∨
      (χ p.2 = 0 ∧ deriv χ p.2 = 0 ∧ deriv (deriv χ) p.2 = 0) := by
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · exact Or.inl ⟨image_eq_zero_of_notMem_tsupport h,
      image_eq_zero_of_notMem_tsupport fun h' => h (tsupport_deriv_subset h')⟩
  · exact Or.inr ⟨image_eq_zero_of_notMem_tsupport h,
      image_eq_zero_of_notMem_tsupport fun h' => h (tsupport_deriv_subset h'),
      image_eq_zero_of_notMem_tsupport fun h' =>
        h (tsupport_deriv_subset (tsupport_deriv_subset h'))⟩

include c0 ct cx cxx hφ hχ sφ sχ in
lemma bounds : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ x : ℝ, |Ft u φ χ t0 τ x| ≤ K ∧
    |Fx u φ χ t0 τ x| ≤ K ∧ |Fxx u φ χ t0 τ x| ≤ K := by
  have hK := sφ.isCompact.prod sχ.isCompact
  have s1 : HasCompactSupport (Function.uncurry (Ft u φ χ t0)) :=
    HasCompactSupport.intro hK fun p hp => by
      rcases zero_off hp with ⟨a, b⟩ | ⟨a, b, -⟩ <;>
        simp [Function.uncurry, Ft, a, b]
  have s2 : HasCompactSupport (Function.uncurry (Fx u φ χ t0)) :=
    HasCompactSupport.intro hK fun p hp => by
      rcases zero_off hp with ⟨a, b⟩ | ⟨a, b, -⟩ <;>
        simp [Function.uncurry, Fx, a, b]
  have s3 : HasCompactSupport (Function.uncurry (Fxx u φ χ t0)) :=
    HasCompactSupport.intro hK fun p hp => by
      rcases zero_off hp with ⟨a, b⟩ | ⟨a, b, c⟩
      · simp [Function.uncurry, Fxx, a]
      · simp [Function.uncurry, Fxx, a, b, c]
  obtain ⟨C1, hC1⟩ := (cont_t t0 c0 ct hφ hχ).bounded_above_of_compact_support s1
  obtain ⟨C2, hC2⟩ := (cont_x t0 c0 cx hφ hχ).bounded_above_of_compact_support s2
  obtain ⟨C3, hC3⟩ := (cont_xx t0 c0 cx cxx hφ hχ).bounded_above_of_compact_support s3
  refine ⟨max (max C1 C2) (max C3 0), le_max_of_le_right (le_max_right _ _), fun τ x => ?_⟩
  have e1 := hC1 (τ, x)
  have e2 := hC2 (τ, x)
  have e3 := hC3 (τ, x)
  simp only [Function.uncurry, Real.norm_eq_abs] at e1 e2 e3
  refine ⟨?_, ?_, ?_⟩
  · exact e1.trans (le_max_of_le_left (le_max_left _ _))
  · exact e2.trans (le_max_of_le_left (le_max_right _ _))
  · exact e3.trans (le_max_of_le_right (le_max_left _ _))

lemma plateau {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V) (hφ1 : ∀ τ ∈ U, φ τ = 1)
    (hχ1 : ∀ x ∈ V, χ x = 1) {τ x : ℝ} (hτ : τ ∈ U) (hx : x ∈ V) :
    F u φ χ t0 τ x = u x (t0 + τ) ∧ Ft u φ χ t0 τ x = ut u x (t0 + τ) ∧
    Fx u φ χ t0 τ x = ux u x (t0 + τ) ∧ Fxx u φ χ t0 τ x = uxx u x (t0 + τ) := by
  have a := hφ1 τ hτ
  have b := deriv_zero_of_eq_one hU hφ1 hτ
  have c := hχ1 x hx
  have d := deriv_zero_of_eq_one hV hχ1 hx
  have e := deriv2_zero_of_eq_one hV hχ1 hx
  simp [F, Ft, Fx, Fxx, a, b, c, d, e]

include c0 hφ hχ in
lemma cont_F : Continuous (Function.uncurry (F u φ χ t0)) := by
  have g : Continuous fun p : ℝ × ℝ => ((p.2, t0 + p.1) : ℝ × ℝ) := by fun_prop
  have cφ : Continuous fun p : ℝ × ℝ => φ p.1 := hφ.continuous.comp continuous_fst
  have cχ : Continuous fun p : ℝ × ℝ => χ p.2 := hχ.continuous.comp continuous_snd
  have cu := c0.comp g
  show Continuous fun p : ℝ × ℝ => F u φ χ t0 p.1 p.2
  unfold F
  exact cφ.mul (cχ.mul cu)

include c0 hφ hχ sφ sχ in
lemma boundF : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ x : ℝ, |F u φ χ t0 τ x| ≤ K := by
  have hK := sφ.isCompact.prod sχ.isCompact
  have s0 : HasCompactSupport (Function.uncurry (F u φ χ t0)) :=
    HasCompactSupport.intro hK fun p hp => by
      rcases zero_off hp with ⟨a, b⟩ | ⟨a, b, -⟩ <;>
        simp [Function.uncurry, F, a, b]
  obtain ⟨C0, hC0⟩ := (cont_F t0 c0 hφ hχ).bounded_above_of_compact_support s0
  refine ⟨max C0 0, le_max_right _ _, fun τ x => ?_⟩
  have e := hC0 (τ, x)
  simp only [Function.uncurry, Real.norm_eq_abs] at e
  exact e.trans (le_max_left _ _)

end Analytic

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

lemma meas_comp {Y : ℝ → Ω → Fin 2 → ℝ} (hYc : ∀ ω, Continuous fun t => Y t ω)
    (hYm : ∀ t, Measurable (Y t)) {g : (Fin 2 → ℝ) → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry fun ω s => g (Y s ω)) := by
  have hj : Measurable (fun q : Ω × ℝ => Y q.2 q.1) :=
    (measurable_uncurry_of_continuous_of_measurable hYc hYm).comp measurable_swap
  exact hg.measurable.comp hj

lemma sq_bdd {P : Measure Ω} [IsProbabilityMeasure P]
    {A : Ω → ℝ → ℝ} {c : ℝ} (h : ∀ ω s, ‖A ω s‖ ≤ c) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _
  have hc : ∀ ω s, (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖c‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    gcongr
    have := h ω s
    exact_mod_cast (show ‖A ω s‖ ≤ ‖c‖ from this.trans (Real.le_norm_self c))
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖A ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hc ω s
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top

end Prog

section ModelFacts
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma vol_eq (m : FeynmanKac.BoundedDiffusionModel P) (x t : ℝ) :
    m.volatility x t = m.augmentedVolatility ![x, t] 0 0 := by
  rw [m.augmentedVolatility_space]; simp

lemma drift_eq (m : FeynmanKac.BoundedDiffusionModel P) (x t : ℝ) :
    m.drift x t = m.augmentedDrift ![x, t] 0 := by
  rw [m.augmentedDrift_space]; simp

lemma vol_cont (m : FeynmanKac.BoundedDiffusionModel P) :
    Continuous fun p : ℝ × ℝ => m.volatility p.1 p.2 := by
  simp only [vol_eq m]
  exact (continuous_apply 0).comp (m.augmentedVolatility_continuous.comp cont_pair)

lemma coef_bdd (m : FeynmanKac.BoundedDiffusionModel P) : ∃ C : ℝ, 0 ≤ C ∧
    (∀ z, |m.augmentedDrift z 0| ≤ C) ∧ (∀ z, |m.augmentedVolatility z 0 0| ≤ C) ∧
    (∀ x t, |m.volatility x t| ≤ C) := by
  obtain ⟨Bd, hBd⟩ := m.augmentedDrift_bounded
  obtain ⟨Bv, hBv⟩ := m.augmentedVolatility_bounded
  have hd : ∀ z, |m.augmentedDrift z 0| ≤ max (max Bd Bv) 0 := fun z =>
    ((norm_le_pi_norm (m.augmentedDrift z) 0).trans (hBd z)).trans
      (le_max_of_le_left (le_max_left _ _))
  have hv : ∀ z, |m.augmentedVolatility z 0 0| ≤ max (max Bd Bv) 0 := fun z =>
    ((norm_le_pi_norm (m.augmentedVolatility z 0) 0).trans (hBv z)).trans
      (le_max_of_le_left (le_max_right _ _))
  exact ⟨_, le_max_right _ _, hd, hv, fun x t => by rw [vol_eq]; exact hv _⟩

end ModelFacts

lemma interval_shift (g : ℝ → ℝ) (t0 s' : ℝ) (hs : 0 ≤ s') :
    ∫ r in t0..t0 + s', g r = ∫ r in Set.Ioc (0 : ℝ) s', g (t0 + r) := by
  have := intervalIntegral.integral_comp_add_left g t0 (a := 0) (b := s')
  rw [add_zero] at this
  rw [← this, intervalIntegral.integral_of_le hs]


lemma prog_add {Ω : Type*} [MeasurableSpace Ω] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {A B : Ω → ℝ → ℝ} (hA : Probability.ProgressivelyMeasurable ℱ A)
    (hB : Probability.ProgressivelyMeasurable ℱ B) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)

/-! ### The path discount as a process in elapsed time -/

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

lemma Dsc_ftc (m : FeynmanKac.BoundedDiffusionModel P) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    Dsc m t ω = 1 + ∫ r in Set.Icc (0 : ℝ) t,
      -(m.potential (m.augmentedPath r ω 0) (m.initialTime + r) * Dsc m r ω) := by
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) t, HasDerivWithinAt (fun τ => Dsc m τ ω)
      (-(gV m ω x * Dsc m x ω)) (Set.Ioi x) x := by
    intro x hx
    have h1 : HasDerivAt (fun τ => ∫ r in (0 : ℝ)..τ, gV m ω r) (gV m ω x) x :=
      ((gV_cont m ω).integral_hasStrictDerivAt 0 x).hasDerivAt
    have h2 := h1.neg.exp
    have heq : (fun τ => Dsc m τ ω) =ᶠ[nhds x]
        (fun τ => Real.exp (-(∫ r in (0 : ℝ)..τ, gV m ω r))) := by
      filter_upwards [lt_mem_nhds hx.1] with τ hτ
      simp [Dsc, Acc, max_eq_left hτ.le]
    have hDx : Dsc m x ω = Real.exp (-(∫ r in (0 : ℝ)..x, gV m ω r)) := by
      simp [Dsc, Acc, max_eq_left hx.1.le]
    rw [hDx, show -(gV m ω x * Real.exp (-(∫ r in (0 : ℝ)..x, gV m ω r))) =
      Real.exp (-(∫ r in (0 : ℝ)..x, gV m ω r)) * -(gV m ω x) by ring]
    exact (h2.congr_of_eventuallyEq heq).hasDerivWithinAt
  have hint : IntervalIntegrable (fun r => -(gV m ω r * Dsc m r ω)) volume 0 t :=
    (((gV_cont m ω).mul (Dsc_cont m ω)).neg).intervalIntegrable 0 t
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (Dsc_cont m ω).continuousOn hderiv hint
  rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc, Dsc_zero] at this
  simp only [gV] at this
  linarith

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

lemma x0_ae (m : FeynmanKac.BoundedDiffusionModel P) :
    ∀ᵐ ω ∂P, m.augmentedPath 0 ω 0 = m.initialState := by
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) _ (dm 0 0) (dp 0 0) (dq 0 0) (le_refl (0 : ℝ))
  filter_upwards [hX.ae_eq 0 le_rfl, hz] with ω e1 e2
  rw [e1]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one,
    m.initialCoordinates_space]
  rw [e2]; simp

end Disc

lemma bd0_aux {a b c d e K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (ha : |a| ≤ K) (hb : |b| ≤ C)
    (hc : |c| ≤ K) (hd : |d| ≤ C) (he : |e| ≤ K) :
    |a + b * c + (1 / 2 : ℝ) * d ^ 2 * e| ≤ K + C * K + C ^ 2 * K := by
  have h1 : |b * c| ≤ C * K := by rw [abs_mul]; exact mul_le_mul hb hc (abs_nonneg _) hC
  have h2 : |d ^ 2| ≤ C ^ 2 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have h3 : |(1 / 2 : ℝ) * d ^ 2 * e| ≤ C ^ 2 * K := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := mul_le_mul h2 he (abs_nonneg _) (by positivity)
    nlinarith [abs_nonneg (d ^ 2), abs_nonneg e, mul_nonneg (abs_nonneg (d ^ 2)) (abs_nonneg e)]
  calc |a + b * c + (1 / 2 : ℝ) * d ^ 2 * e|
      ≤ |a + b * c| + |(1 / 2 : ℝ) * d ^ 2 * e| := abs_add_le _ _
    _ ≤ |a| + |b * c| + |(1 / 2 : ℝ) * d ^ 2 * e| := by gcongr; exact abs_add_le _ _
    _ ≤ K + C * K + C ^ 2 * K := by linarith

set_option maxHeartbeats 4000000 in
lemma main_case {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsClassicalPDESolution u)
    (hdisc : m.AdmissibleDiscountedGradient u)
    (s' : ℝ) (hs'0 : 0 < s') (hs'T : s' ≤ m.terminalTime - m.initialTime)
    (R : ℝ) (hx₀R : |m.initialState| < R) :
    ∀ᵐ ω ∂P, ((s' : ℝ) : WithTop ℝ) <
        Probability.exitTime (fun ω r => m.augmentedPath r ω 0) R ω →
      m.discountedReward u (m.initialTime + s') ω =
        u m.initialState m.initialTime +
          stochasticIntegralBrownian (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
            (m.discountedGradientIntegrand u) hdisc.1 hdisc.2.1 hdisc.2.2 s' ω := by
  obtain ⟨⟨h1, h2, h3, c0, ct, cx, cxx⟩, -, -, hpde⟩ := hu
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hYc : ∀ ω, Continuous fun t => m.augmentedPath t ω := hX.continuous_path
  have hYa : ∀ t, Measurable[m.filtration t] (m.augmentedPath t) := fun t =>
    (hX.adapted t).measurable
  have hYm : ∀ t, Measurable (m.augmentedPath t) := fun t =>
    (hYa t).mono (m.filtration.le t) le_rfl
  have hXc : ∀ ω, Continuous fun r => m.augmentedPath r ω 0 := fun ω =>
    (continuous_apply 0).comp (hYc ω)
  have hXa : ∀ t, Measurable[m.filtration t] (fun ω => m.augmentedPath t ω 0) := fun t =>
    (measurable_pi_apply 0).comp (hYa t)
  obtain ⟨φ, hφ, sφ, hφ1⟩ := cutoff 0 (m.terminalTime - m.initialTime)
  obtain ⟨χ, hχ, sχ, hχ1⟩ := cutoff (-R) R
  obtain ⟨K, hK0, hKb⟩ := bounds m.initialTime c0 ct cx cxx hφ hχ sφ sχ
  obtain ⟨C, hC0, hCd, hCv, hCvol⟩ := coef_bdd m
  obtain ⟨BV, hBV0, hBV⟩ := pot_bdd m
  have cfx := cont_x m.initialTime c0 cx hφ hχ
  have cF := cont_F m.initialTime c0 hφ hχ
  have hcd : Continuous fun z : Fin 2 → ℝ => m.augmentedDrift z 0 :=
    (continuous_apply 0).comp m.augmentedDrift_continuous
  have hμm : Measurable (Function.uncurry fun ω r => m.augmentedDrift (m.augmentedPath r ω) 0) :=
    meas_comp hYc hYm hcd
  have hμp : Probability.ProgressivelyMeasurable m.filtration
      (fun ω r => m.augmentedDrift (m.augmentedPath r ω) 0) :=
    ItoLemma.continuous_adapted_composition_progressive hYc hYa hcd
  have hσm := dm 0 0
  have hσp := dp 0 0
  have hσq := dq 0 0
  have hXrep : ∀ t : ℝ, 0 ≤ t →
      (fun ω => m.augmentedPath t ω 0) =ᵐ[P]
        (fun ω => m.initialState +
          (∫ r in Set.Icc (0 : ℝ) t, m.augmentedDrift (m.augmentedPath r ω) 0 ∂volume) +
          stochasticIntegralBrownian (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
            (fun ω r => m.augmentedVolatility (m.augmentedPath r ω) 0 0) hσm hσp hσq t ω) := by
    intro t ht
    filter_upwards [hX.ae_eq t ht] with ω hω
    rw [hω]
    simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one,
      m.initialCoordinates_space]
  have hJm : Measurable (Function.uncurry fun ω r =>
      Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
        m.augmentedVolatility (m.augmentedPath r ω) 0 0) :=
    (meas_time hYc hYm cfx).mul hσm
  have hJp : Probability.ProgressivelyMeasurable m.filtration (fun ω r =>
      Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
        m.augmentedVolatility (m.augmentedPath r ω) 0 0) :=
    Probability.ProgressivelyMeasurable.mul (prog_time hYc hYa cfx) hσp
  have hJb : ∀ ω r, ‖Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
      m.augmentedVolatility (m.augmentedPath r ω) 0 0‖ ≤ K * C := fun ω r => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hKb _ _).2.1 (hCv _) (abs_nonneg _) hK0
  have hJq := sq_bdd (P := P) hJb
  have itoAll := fun (t : ℝ) (ht : 0 ≤ t) =>
    ItoLemma.ito_formula_time_dependent_bounded (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) m.initialState
    (fun ω r => m.augmentedDrift (m.augmentedPath r ω) 0)
    (fun ω r => m.augmentedVolatility (m.augmentedPath r ω) 0 0)
    hμm hμp hσm hσp hσq hC0 (fun ω r => hCd _) (fun ω r => hCv _)
    (fun r ω => m.augmentedPath r ω 0) hXc hXa hXrep
    (F u φ χ m.initialTime) (Ft u φ χ m.initialTime) (Fx u φ χ m.initialTime)
    (Fxx u φ χ m.initialTime)
    (hasDeriv_t m.initialTime h2 hφ) (hasDeriv_x m.initialTime h1 hχ)
    (hasDeriv_xx m.initialTime h1 h3 hχ)
    (cont_t m.initialTime c0 ct hφ hχ) cfx (cont_xx m.initialTime c0 cx cxx hφ hχ)
    hK0 hKb hJm hJp hJq ht
  -- the two-dimensional process (truncated value, discount)
  set Z : ℝ → Ω → Fin 2 → ℝ := fun τ ω =>
    ![F u φ χ m.initialTime τ (m.augmentedPath τ ω 0), Dsc m τ ω] with hZdef
  have hZc : ∀ ω, Continuous fun t => Z t ω := fun ω => by
    refine continuous_pi fun i => ?_
    fin_cases i
    · show Continuous fun t => F u φ χ m.initialTime t (m.augmentedPath t ω 0)
      exact cF.comp (continuous_id.prodMk (hXc ω))
    · exact Dsc_cont m ω
  have hZa : ∀ t, Measurable[m.filtration t] (Z t) := fun t => by
    have a0 : Measurable[m.filtration t] fun ω =>
        F u φ χ m.initialTime t (m.augmentedPath t ω 0) :=
      cF.measurable.comp (measurable_const.prodMk (hXa t))
    have a1 := Dsc_meas m t
    letI : MeasurableSpace Ω := m.filtration t
    exact measurable_pi_lambda _ fun i => by fin_cases i; exacts [a0, a1]
  have hZm : ∀ t, Measurable (Z t) := fun t => (hZa t).mono (m.filtration.le t) le_rfl
  have hZim : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i) := fun i =>
    meas_comp hZc hZm (continuous_apply i)
  have hZip : ∀ i, Probability.ProgressivelyMeasurable m.filtration (fun ω s => Z s ω i) :=
    fun i => ItoLemma.continuous_adapted_composition_progressive hZc hZa (continuous_apply i)
  set J : Ω → ℝ → ℝ := fun ω r => Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
        m.augmentedVolatility (m.augmentedPath r ω) 0 0 with hJdef
  set Hh : Fin 2 → Fin 1 → Ω → ℝ → ℝ := fun p _ => ![J, fun _ _ => (0 : ℝ)] p with hHhdef
  have hHm : ∀ p k, Measurable (Function.uncurry (Hh p k)) := by
    intro p k; fin_cases p
    · exact hJm
    · exact measurable_const
  have hHp : ∀ p k, Probability.ProgressivelyMeasurable m.filtration (Hh p k) := by
    intro p k; fin_cases p
    · exact hJp
    · exact ItoLemma.continuous_adapted_composition_progressive hYc hYa continuous_const
  have hHb : ∀ p k ω s, |Hh p k ω s| ≤ K * C := by
    intro p k ω s; fin_cases p
    · exact hJb ω s
    · show |(0 : ℝ)| ≤ K * C
      simpa using mul_nonneg hK0 hC0
  have hHs : ∀ (p : Fin 2) (k : Fin 1) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Hh p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p k => sq_bdd (P := P) (c := K * C) fun ω s => hHb p k ω s
  set b0 : Ω → ℝ → ℝ := fun ω s =>
    Ft u φ χ m.initialTime s (m.augmentedPath s ω 0) +
      m.augmentedDrift (m.augmentedPath s ω) 0 * Fx u φ χ m.initialTime s (m.augmentedPath s ω 0) +
      (1 / 2 : ℝ) * (m.augmentedVolatility (m.augmentedPath s ω) 0 0) ^ 2 *
        Fxx u φ χ m.initialTime s (m.augmentedPath s ω 0) with hb0def
  set b1 : Ω → ℝ → ℝ := fun ω r =>
    -(m.potential (m.augmentedPath r ω 0) (m.initialTime + r) * Dsc m r ω) with hb1def
  set bd : Fin 2 → Ω → ℝ → ℝ := ![b0, b1] with hbddef
  set Z0 : Ω → Fin 2 → ℝ := fun _ => ![F u φ χ m.initialTime 0 m.initialState, 1] with hZ0def
  have hver : IsVectorItoVersion m.brownian m.filtration m.brownianFiltration Hh hHm hHp hHs
      Z0 bd Z := by
    refine ⟨hZc, fun t => (hZa t).stronglyMeasurable, fun t ht => ?_⟩
    have hz := stochasticIntegralBrownian_ae_zero_readable (m.brownian.W 0) m.filtration
      (m.brownianFiltration 0) (hHm 1 0) (hHp 1 0) (hHs 1 0) t
    filter_upwards [itoAll t ht, hz] with ω e1 e2
    have f0 : Z t ω 0 = vectorItoProcess m.brownian m.filtration m.brownianFiltration Hh hHm
        hHp hHs Z0 bd t ω 0 := by
      simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one]
      rw [integral_Icc_eq_integral_Ioc, add_assoc]
      exact sub_eq_iff_eq_add'.1 e1
    have f1 : Z t ω 1 = vectorItoProcess m.brownian m.filtration m.brownianFiltration Hh hHm
        hHp hHs Z0 bd t ω 1 := by
      simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one]
      have e2' := e2
      simp only [Pi.zero_apply] at e2'
      rw [show stochasticIntegralBrownian (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
        (Hh 1 0) (hHm 1 0) (hHp 1 0) (hHs 1 0) t ω = 0 from e2', add_zero]
      exact Dsc_ftc m ω ht
    funext p
    fin_cases p
    · exact f0
    · exact f1
  have hbm : ∀ p : Fin 2, Measurable (Function.uncurry (bd p)) := by
    have m0 : Measurable (Function.uncurry b0) :=
      ((meas_time hYc hYm (cont_t m.initialTime c0 ct hφ hχ)).add
        (hμm.mul (meas_time hYc hYm cfx))).add
        ((measurable_const.mul (hσm.pow_const 2)).mul
          (meas_time hYc hYm (cont_xx m.initialTime c0 cx cxx hφ hχ)))
    have m1 : Measurable (Function.uncurry b1) :=
      ((meas_time hYc hYm (pot_cont m)).mul (hZim 1)).neg
    intro p; fin_cases p
    · exact m0
    · exact m1
  have hB : ∀ p ω s, |bd p ω s| ≤ K + C * K + C ^ 2 * K + BV := by
    intro p ω s
    fin_cases p
    · show |b0 ω s| ≤ _
      have hk := hKb s (m.augmentedPath s ω 0)
      have := bd0_aux hK0 hC0 hk.1 (hCd (m.augmentedPath s ω)) hk.2.1
        (hCv (m.augmentedPath s ω)) hk.2.2
      exact this.trans (le_add_of_nonneg_right hBV0)
    · show |b1 ω s| ≤ _
      have : |b1 ω s| ≤ BV := by
        show |-(m.potential (m.augmentedPath s ω 0) (m.initialTime + s) * Dsc m s ω)| ≤ BV
        rw [abs_neg, abs_mul]
        have := mul_le_mul (hBV (m.augmentedPath s ω 0) (m.initialTime + s))
          (Dsc_abs_le m s ω) (abs_nonneg _) hBV0
        linarith
      have : 0 ≤ K + C * K + C ^ 2 * K := by positivity
      linarith
  have hplusm : ∀ p q k, Measurable (Function.uncurry
      fun ω s => Hh p k ω s + Hh q k ω s) := fun p q k => (hHm p k).add (hHm q k)
  have hplusp : ∀ p q k, Probability.ProgressivelyMeasurable m.filtration
      (fun ω s => Hh p k ω s + Hh q k ω s) := fun p q k => prog_add (hHp p k) (hHp q k)
  have hplusq : ∀ (p q : Fin 2) (k : Fin 1) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Hh p k ω s + Hh q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p q k => sq_bdd (P := P) (c := K * C + K * C) fun ω s => (norm_add_le _ _).trans
      (add_le_add (by rw [Real.norm_eq_abs]; exact hHb p k ω s)
        (by rw [Real.norm_eq_abs]; exact hHb q k ω s))
  have hJm2 : ∀ k : Fin 1, Measurable (Function.uncurry
      fun ω s => Z s ω 1 * Hh 0 k ω s + Z s ω 0 * Hh 1 k ω s) :=
    fun k => ((hZim 1).mul (hHm 0 k)).add ((hZim 0).mul (hHm 1 k))
  have hJp2 : ∀ k : Fin 1, Probability.ProgressivelyMeasurable m.filtration
      (fun ω s => Z s ω 1 * Hh 0 k ω s + Z s ω 0 * Hh 1 k ω s) :=
    fun k => prog_add ((hZip 1).mul (hHp 0 k)) ((hZip 0).mul (hHp 1 k))
  have hJb2 : ∀ (k : Fin 1) ω s, ‖Z s ω 1 * Hh 0 k ω s + Z s ω 0 * Hh 1 k ω s‖ ≤ K * C := by
    intro k ω s
    show ‖Dsc m s ω * J ω s + Z s ω 0 * 0‖ ≤ K * C
    rw [mul_zero, add_zero, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := hJb ω s
    rw [Real.norm_eq_abs] at this
    calc |Dsc m s ω| * |J ω s| ≤ 1 * (K * C) :=
          mul_le_mul (Dsc_abs_le m s ω) this (abs_nonneg _) zero_le_one
      _ = K * C := one_mul _
  have hJq2 : ∀ (k : Fin 1) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Z s ω 1 * Hh 0 k ω s + Z s ω 0 * Hh 1 k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun k => sq_bdd (P := P) (hJb2 k)
  have hX₀m : ∀ p : Fin 2, Measurable fun ω => Z0 ω p := fun p => measurable_const
  obtain ⟨KF, hKF0, hKF⟩ := boundF m.initialTime c0 hφ hχ sφ sχ
  have hZR : ∀ ω s, s ∈ Set.Icc (0 : ℝ) s' → ‖Z s ω‖ < KF + 2 := by
    intro ω s _
    refine (pi_norm_lt_iff (by linarith)).2 fun i => ?_
    fin_cases i
    · show ‖F u φ χ m.initialTime s (m.augmentedPath s ω 0)‖ < KF + 2
      rw [Real.norm_eq_abs]; linarith [hKF s (m.augmentedPath s ω 0)]
    · show ‖Dsc m s ω‖ < KF + 2
      rw [Real.norm_eq_abs]; linarith [Dsc_abs_le m s ω]
  have prod := ItoCalculusII.continuous_product_rule_bounded_state m.brownian m.filtration
    m.brownianFiltration Hh hHm hHp hHs Z0 bd Z hver hX₀m hbm
    (B := K + C * K + C ^ 2 * K + BV) (by positivity) (mul_nonneg hK0 hC0) hB hHb
    hplusm hplusp hplusq hJm2 hJp2 hJq2 hs'0 (KF + 2) (by linarith) hZR
  -- the intermediate integrand with deterministic clock
  have hg2 : Continuous (Function.uncurry fun r x =>
      Fx u φ χ m.initialTime r x * m.volatility x (m.initialTime + r)) := by
    have hpp : Continuous fun p : ℝ × ℝ => ((p.2, m.initialTime + p.1) : ℝ × ℝ) := by fun_prop
    exact cfx.mul ((vol_cont m).comp hpp)
  have h2m : Measurable (Function.uncurry fun ω r => Dsc m r ω *
      (Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
        m.volatility (m.augmentedPath r ω 0) (m.initialTime + r))) :=
    (hZim 1).mul (meas_time hYc hYm hg2)
  have h2p : Probability.ProgressivelyMeasurable m.filtration (fun ω r => Dsc m r ω *
      (Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
        m.volatility (m.augmentedPath r ω 0) (m.initialTime + r))) :=
    (hZip 1).mul (prog_time hYc hYa hg2)
  have h2b : ∀ ω r, ‖Dsc m r ω * (Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
      m.volatility (m.augmentedPath r ω 0) (m.initialTime + r))‖ ≤ K * C := fun ω r => by
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    have := mul_le_mul (hKb r (m.augmentedPath r ω 0)).2.1
      (hCvol (m.augmentedPath r ω 0) (m.initialTime + r)) (abs_nonneg _) hK0
    calc |Dsc m r ω| * (|Fx u φ χ m.initialTime r (m.augmentedPath r ω 0)| *
          |m.volatility (m.augmentedPath r ω 0) (m.initialTime + r)|) ≤ 1 * (K * C) :=
          mul_le_mul (Dsc_abs_le m r ω) this (by positivity) zero_le_one
      _ = K * C := one_mul _
  have h2q := sq_bdd (P := P) h2b
  have hclk := clock m
  have stepA := si_congr_ae (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    (hJm2 0) (hJp2 0) (hJq2 0) h2m h2p h2q
    (sq_bdd (P := P) (c := K * C + K * C) fun ω r => (norm_sub_le _ _).trans
      (add_le_add (hJb2 0 ω r) (h2b ω r))) hs'0
    (by
      filter_upwards [hclk] with ω hω r hr _
      show Dsc m r ω * J ω r + Z r ω 0 * 0 = _
      simp only [hJdef, m.augmentedVolatility_space, hω r hr.le, mul_zero, add_zero])
  have hτ : IsStoppingTime m.filtration (fun ω =>
      min (Probability.exitTime (fun ω r => m.augmentedPath r ω 0) R ω)
        (((m.terminalTime - m.initialTime : ℝ)) : WithTop ℝ)) :=
    IsStoppingTime.min (exit_isStoppingTime m.filtration _ hXc hXa R) (isStoppingTime_const _ _)
  have stepB := stochasticIntegralBrownian_congr_of_le_readable _ (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) hτ h2m h2p h2q hdisc.1 hdisc.2.1 hdisc.2.2 (fun ω r hr hrτ => by
      rw [le_min_iff] at hrτ
      have hb := Probability.norm_le_of_le_exitTime_readable (hXc ω) hr hrτ.1
      have hrT : r ≤ m.terminalTime - m.initialTime := WithTop.coe_le_coe.1 hrτ.2
      rw [Real.norm_eq_abs, abs_le] at hb
      have pl := plateau (u := u) m.initialTime isOpen_Ioo isOpen_Ioo hφ1 hχ1
        (τ := r) (x := m.augmentedPath r ω 0) ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩
      unfold FeynmanKac.BoundedDiffusionModel.discountedGradientIntegrand
        FeynmanKac.BoundedDiffusionModel.spaceGradientIntegrand
      rw [if_pos ⟨hr.le, hrT⟩, pl.2.2.1, FeynmanKac.BoundedDiffusionModel.pathDiscount,
        pd_eq m ω hr.le]
      simp only [FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left, ux]
      ring) hs'0
  filter_upwards [prod, stepA, stepB, hclk, x0_ae m] with ω e1 e2 e3 e4 e5 hlt
  have hle : ((s' : ℝ) : WithTop ℝ) ≤ min (Probability.exitTime
      (fun ω r => m.augmentedPath r ω 0) R ω) (((m.terminalTime - m.initialTime : ℝ)) : WithTop ℝ) :=
    le_min hlt.le (WithTop.coe_le_coe.2 hs'T)
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) s', ‖m.augmentedPath r ω 0‖ < R := by
    have := not_le.2 hlt
    rw [Probability.exitTime_le_iff_readable (hXc ω)] at this
    push_neg at this
    exact this
  have hpl : ∀ r ∈ Set.Icc (0 : ℝ) s', ∀ x : ℝ, |x| < R →
      F u φ χ m.initialTime r x = u x (m.initialTime + r) ∧
      Ft u φ χ m.initialTime r x = ut u x (m.initialTime + r) ∧
      Fx u φ χ m.initialTime r x = ux u x (m.initialTime + r) ∧
      Fxx u φ χ m.initialTime r x = uxx u x (m.initialTime + r) := by
    intro r hr x hx
    rw [abs_lt] at hx
    exact plateau (u := u) m.initialTime isOpen_Ioo isOpen_Ioo hφ1 hχ1
      ⟨by linarith [hr.1], by linarith [hr.2]⟩ ⟨by linarith, by linarith⟩
  have eF1 := (hpl s' ⟨hs'0.le, le_rfl⟩ _ (by simpa using hbd s' ⟨hs'0.le, le_rfl⟩)).1
  have eF0 := (hpl 0 ⟨le_rfl, hs'0.le⟩ _ hx₀R).1
  rw [add_zero] at eF0
  have hZs0 : Z s' ω 0 = u (m.path (m.initialTime + s') ω) (m.initialTime + s') := by
    show F u φ χ m.initialTime s' (m.augmentedPath s' ω 0) = _
    simp only [FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left]
    exact eF1
  have hZs1 : Z s' ω 1 = FeynmanKac.pathDiscount m.path m.potential m.initialTime
      (m.initialTime + s') ω := (pd_eq m ω hs'0.le).symm
  have hZ00 : Z 0 ω 0 = u m.initialState m.initialTime := by
    show F u φ χ m.initialTime 0 (m.augmentedPath 0 ω 0) = _
    rw [e5]; exact eF0
  have hZ01 : Z 0 ω 1 = 1 := Dsc_zero m ω
  have hI : ∫ s in Set.Ioc (0 : ℝ) s', (Z s ω 1 * bd 0 ω s + Z s ω 0 * bd 1 ω s +
      ∑ k : Fin 1, Hh 0 k ω s * Hh 1 k ω s) =
      -∫ r in Set.Ioc (0 : ℝ) s', Dsc m r ω *
        m.runningSource (m.augmentedPath r ω 0) (m.initialTime + r) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    have hr' : r ∈ Set.Icc 0 s' := Set.Ioc_subset_Icc_self hr
    have hb := hbd r hr'
    rw [Real.norm_eq_abs] at hb
    obtain ⟨q0, q1, q2, q3⟩ := hpl r hr' _ hb
    show Dsc m r ω * b0 ω r + F u φ χ m.initialTime r (m.augmentedPath r ω 0) * b1 ω r +
      ∑ k : Fin 1, J ω r * 0 = _
    simp only [hb0def, hb1def, q0, q1, q2, q3, m.augmentedDrift_space,
      m.augmentedVolatility_space, e4 r hr'.1, ut, ux, uxx, mul_zero, Finset.sum_const_zero,
      add_zero]
    have hP := hpde (m.augmentedPath r ω 0) (m.initialTime + r)
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
    linear_combination (Dsc m r ω) * hP
  have hR : ∫ r in m.initialTime..(m.initialTime + s'),
      FeynmanKac.pathDiscount m.path m.potential m.initialTime r ω *
        m.runningSource (m.path r ω) r =
      ∫ r in Set.Ioc (0 : ℝ) s', Dsc m r ω *
        m.runningSource (m.augmentedPath r ω 0) (m.initialTime + r) := by
    rw [interval_shift (fun r => FeynmanKac.pathDiscount m.path m.potential m.initialTime r ω *
        m.runningSource (m.path r ω) r) _ _ hs'0.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    simp only [pd_eq m ω hr.1.le, FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left]
  simp only [Fin.sum_univ_one] at e1
  rw [hZs0, hZs1, hZ00, hZ01] at e1
  simp only [Fin.sum_univ_one] at hI
  rw [hI] at e1
  simp only [FeynmanKac.BoundedDiffusionModel.discountedReward, FeynmanKac.discountedReward]
  rw [hR, ← e3 hle, ← e2]
  linarith

end S87H

open S87H in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hdisc : m.AdmissibleDiscountedGradient u)
    (s : ℝ) (hs : s ∈ Set.Icc m.initialTime m.terminalTime) :
    (fun ω => m.discountedReward u s ω) =ᵐ[P]
      (fun ω => u m.initialState m.initialTime +
        m.discountedGradientItoIntegral u hdisc s ω) := by
  obtain ⟨hs1, hs2⟩ := hs
  simp only [FeynmanKac.BoundedDiffusionModel.discountedGradientItoIntegral]
  rcases eq_or_lt_of_le hs1 with h | h
  · subst h
    rw [sub_self]
    have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (m.brownian.W 0) m.filtration
      (m.brownianFiltration 0) _ hdisc.1 hdisc.2.1 hdisc.2.2 (le_refl (0 : ℝ))
    filter_upwards [x0_ae m, hz] with ω e1 e2
    rw [e2]
    simp [FeynmanKac.BoundedDiffusionModel.discountedReward, FeynmanKac.discountedReward,
      FeynmanKac.pathDiscount, FeynmanKac.BoundedDiffusionModel.path, e1]
  · obtain ⟨s', rfl⟩ : ∃ s', s = m.initialTime + s' := ⟨s - m.initialTime, by ring⟩
    have hs'0 : 0 < s' := by linarith
    have hs'T : s' ≤ m.terminalTime - m.initialTime := by linarith
    rw [show m.initialTime + s' - m.initialTime = s' by ring]
    have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, |m.initialState| < (k : ℝ) →
        ((s' : ℝ) : WithTop ℝ) < Probability.exitTime
          (fun ω r => m.augmentedPath r ω 0) (k : ℝ) ω →
        m.discountedReward u (m.initialTime + s') ω =
          u m.initialState m.initialTime +
            LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
              (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
              (m.discountedGradientIntegrand u) hdisc.1 hdisc.2.1 hdisc.2.2 s' ω := by
      refine ae_all_iff.2 fun k => ?_
      by_cases hk : |m.initialState| < (k : ℝ)
      · filter_upwards [main_case P m u hu hdisc s' hs'0 hs'T k hk] with ω hω _
        exact hω
      · exact Filter.Eventually.of_forall fun ω h' => absurd h' hk
    obtain ⟨_, _, _, hX⟩ := m.isDiffusion
    filter_upwards [hall] with ω hω
    obtain ⟨K, hK⟩ := Probability.exists_lt_exitTime_readable
      (X := fun ω r => m.augmentedPath r ω 0) (ω := ω)
      ((continuous_apply 0).comp (hX.continuous_path ω)) hs'0.le
    have hk : |m.initialState| < ((max K (⌈|m.initialState|⌉₊ + 1) : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil |m.initialState|
      have h2 : ((⌈|m.initialState|⌉₊ + 1 : ℕ) : ℝ) ≤
          ((max K (⌈|m.initialState|⌉₊ + 1) : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
      push_cast at h2 ⊢
      linarith
    exact hω _ hk (hK _ (le_max_left _ _))
