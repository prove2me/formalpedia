-- Prove2me | solution 1 for FeynmanKac.space_time_ito_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T18:04:56.280672+00:00
-- url     : https://prove2.me/submissions/ab6fbc0d-edf1-4a95-995e-a510a585d396

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
import Mathlib

open MeasureTheory ProbabilityTheory
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito
open scoped NNReal ENNReal

namespace S87F

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

set_option maxHeartbeats 1600000 in
lemma main_case {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsC12 u)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (r : ℝ),
      H ω r =
        if r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime) then
          m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) *
            deriv (fun x => u x (m.initialTime + r))
              (m.path (m.initialTime + r) ω)
        else 0)
    (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration H)
    (hq : ∀ (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
        (‖H ω r‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
    (s' : ℝ) (hs'0 : 0 < s') (hs'T : s' ≤ m.terminalTime - m.initialTime)
    (R : ℝ) (hx₀R : |m.initialState| < R) :
    ∀ᵐ ω ∂P, ((s' : ℝ) : WithTop ℝ) <
        Probability.exitTime (fun ω r => m.augmentedPath r ω 0) R ω →
      u (m.path (m.initialTime + s') ω) (m.initialTime + s') -
          u m.initialState m.initialTime =
        (∫ r in m.initialTime..(m.initialTime + s'),
            deriv (fun q => u (m.path r ω) q) r +
            m.drift (m.path r ω) r * deriv (fun x => u x r) (m.path r ω) +
            (1 / 2 : ℝ) * (m.volatility (m.path r ω) r) ^ 2 *
              deriv (deriv (fun x => u x r)) (m.path r ω)) +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
          H hm hp hq s' ω := by
  obtain ⟨h1, h2, h3, c0, ct, cx, cxx⟩ := hu
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
  have cfx := cont_x m.initialTime c0 cx hφ hχ
  -- coefficients
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
  -- representation of the space coordinate
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
  -- integrand of the Itô formula
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
  have ito := ItoLemma.ito_formula_time_dependent_bounded (m.brownian.W 0) m.filtration
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
    hK0 hKb hJm hJp hJq hs'0.le
  -- the intermediate integrand with deterministic clock
  have hg2 : Continuous (Function.uncurry fun r x =>
      Fx u φ χ m.initialTime r x * m.volatility x (m.initialTime + r)) := by
    have hpp : Continuous fun p : ℝ × ℝ => ((p.2, m.initialTime + p.1) : ℝ × ℝ) := by fun_prop
    exact cfx.mul ((vol_cont m).comp hpp)
  have h2m := meas_time hYc hYm hg2
  have h2p := prog_time hYc hYa hg2
  have h2b : ∀ ω r, ‖Fx u φ χ m.initialTime r (m.augmentedPath r ω 0) *
      m.volatility (m.augmentedPath r ω 0) (m.initialTime + r)‖ ≤ K * C := fun ω r => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hKb _ _).2.1 (hCvol _ _) (abs_nonneg _) hK0
  have h2q := sq_bdd (P := P) h2b
  have hclk := clock m
  have stepA := si_congr_ae (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
    hJm hJp hJq h2m h2p h2q
    (sq_bdd (P := P) (c := K * C + K * C) fun ω r => (norm_sub_le _ _).trans
      (add_le_add (hJb ω r) (h2b ω r))) hs'0
    (by
      filter_upwards [hclk] with ω hω r hr _
      rw [m.augmentedVolatility_space, hω r hr.le])
  -- locality up to the exit time
  have hτ : IsStoppingTime m.filtration (fun ω =>
      min (Probability.exitTime (fun ω r => m.augmentedPath r ω 0) R ω)
        (((m.terminalTime - m.initialTime : ℝ)) : WithTop ℝ)) :=
    IsStoppingTime.min (exit_isStoppingTime m.filtration _ hXc hXa R) (isStoppingTime_const _ _)
  have stepB := stochasticIntegralBrownian_congr_of_le_readable _ (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) hτ h2m h2p h2q hm hp hq (fun ω r hr hrτ => by
      rw [le_min_iff] at hrτ
      have hb := Probability.norm_le_of_le_exitTime_readable (hXc ω) hr hrτ.1
      have hrT : r ≤ m.terminalTime - m.initialTime := WithTop.coe_le_coe.1 hrτ.2
      rw [Real.norm_eq_abs, abs_le] at hb
      have pl := plateau (u := u) m.initialTime isOpen_Ioo isOpen_Ioo hφ1 hχ1
        (τ := r) (x := m.augmentedPath r ω 0) ⟨by linarith, by linarith⟩
        ⟨by linarith, by linarith⟩
      rw [hH, if_pos ⟨hr.le, hrT⟩, pl.2.2.1]
      simp only [FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left, ux]
      ring) hs'0
  filter_upwards [ito, stepA, stepB, hclk] with ω e1 e2 e3 e4 hlt
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
  simp only [FeynmanKac.BoundedDiffusionModel.path, add_sub_cancel_left]
  rw [← eF1, ← eF0, e1, e2, e3 hle]
  rw [interval_shift _ m.initialTime s' hs'0.le]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
  have hr' : r ∈ Set.Icc 0 s' := Set.Ioc_subset_Icc_self hr
  have hb := hbd r hr'
  rw [Real.norm_eq_abs] at hb
  obtain ⟨-, q1, q2, q3⟩ := hpl r hr' _ hb
  simp only [q1, q2, q3, m.augmentedDrift_space, m.augmentedVolatility_space, e4 r hr'.1, ut, ux,
    uxx, add_sub_cancel_left]

lemma zero_case {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) (u : ℝ → ℝ → ℝ) :
    ∀ᵐ ω ∂P, u (m.path m.initialTime ω) m.initialTime - u m.initialState m.initialTime = 0 := by
  obtain ⟨dm, dp, dq, hX⟩ := m.isDiffusion
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (m.brownian.W 0) m.filtration
    (m.brownianFiltration 0) _ (dm 0 0) (dp 0 0) (dq 0 0) (le_refl (0 : ℝ))
  filter_upwards [hX.ae_eq 0 le_rfl, hz] with ω e1 e2
  simp only [FeynmanKac.BoundedDiffusionModel.path, sub_self]
  rw [e1]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, Fin.sum_univ_one,
    m.initialCoordinates_space]
  rw [e2]
  simp

end S87F

open S87F in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ) (hu : m.IsC12 u)
    (H : Ω → ℝ → ℝ)
    (hH : ∀ (ω : Ω) (r : ℝ),
      H ω r =
        if r ∈ Set.Icc (0 : ℝ) (m.terminalTime - m.initialTime) then
          m.volatility (m.path (m.initialTime + r) ω) (m.initialTime + r) *
            deriv (fun x => u x (m.initialTime + r))
              (m.path (m.initialTime + r) ω)
        else 0)
    (hm : Measurable (Function.uncurry H))
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable m.filtration H)
    (hq : ∀ (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T,
        (‖H ω r‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
    (s : ℝ) (hs : s ∈ Set.Icc m.initialTime m.terminalTime) :
    (fun ω => u (m.path s ω) s - u m.initialState m.initialTime) =ᵐ[P]
      (fun ω =>
        (∫ r in m.initialTime..s,
            deriv (fun q => u (m.path r ω) q) r +
            m.drift (m.path r ω) r * deriv (fun x => u x r) (m.path r ω) +
            (1 / 2 : ℝ) * (m.volatility (m.path r ω) r) ^ 2 *
              deriv (deriv (fun x => u x r)) (m.path r ω)) +
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
          (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
          H hm hp hq (s - m.initialTime) ω) := by
  obtain ⟨hs1, hs2⟩ := hs
  rcases eq_or_lt_of_le hs1 with h | h
  · subst h
    have hz := stochasticIntegralBrownian_ae_zero_of_nonpos (m.brownian.W 0) m.filtration
      (m.brownianFiltration 0) H hm hp hq (le_refl (0 : ℝ))
    rw [sub_self]
    filter_upwards [zero_case P m u, hz] with ω e1 e2
    rw [e1, e2, intervalIntegral.integral_same]
    simp
  · obtain ⟨s', rfl⟩ : ∃ s', s = m.initialTime + s' := ⟨s - m.initialTime, by ring⟩
    have hs'0 : 0 < s' := by linarith
    have hs'T : s' ≤ m.terminalTime - m.initialTime := by linarith
    rw [show m.initialTime + s' - m.initialTime = s' by ring]
    have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, |m.initialState| < (k : ℝ) →
        ((s' : ℝ) : WithTop ℝ) < Probability.exitTime
          (fun ω r => m.augmentedPath r ω 0) (k : ℝ) ω →
        u (m.path (m.initialTime + s') ω) (m.initialTime + s') -
            u m.initialState m.initialTime =
          (∫ r in m.initialTime..(m.initialTime + s'),
              deriv (fun q => u (m.path r ω) q) r +
              m.drift (m.path r ω) r * deriv (fun x => u x r) (m.path r ω) +
              (1 / 2 : ℝ) * (m.volatility (m.path r ω) r) ^ 2 *
                deriv (deriv (fun x => u x r)) (m.path r ω)) +
          LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian
            (m.brownian.W 0) m.filtration (m.brownianFiltration 0)
            H hm hp hq s' ω := by
      refine ae_all_iff.2 fun k => ?_
      by_cases hk : |m.initialState| < (k : ℝ)
      · filter_upwards [main_case P m u hu H hH hm hp hq s' hs'0 hs'T k hk] with ω hω _
        exact hω
      · exact Filter.Eventually.of_forall fun ω h' => absurd h' hk
    obtain ⟨_, _, _, hX⟩ := m.isDiffusion
    filter_upwards [hall] with ω hω
    obtain ⟨K, hK⟩ := Probability.exists_lt_exitTime_readable
      (X := fun ω r => m.augmentedPath r ω 0) (ω := ω)
      ((continuous_apply 0).comp (hX.continuous_path ω)) hs'0.le
    have hk : |m.initialState| < ((max K (⌈|m.initialState|⌉₊ + 1) : ℕ) : ℝ) := by
      have h1 := Nat.le_ceil |m.initialState|
      have h2 : ((⌈|m.initialState|⌉₊ + 1 : ℕ) : ℝ) ≤ ((max K (⌈|m.initialState|⌉₊ + 1) : ℕ) : ℝ) :=
        by exact_mod_cast le_max_right _ _
      push_cast at h2 ⊢
      linarith
    exact hω _ hk (hK _ (le_max_left _ _))
