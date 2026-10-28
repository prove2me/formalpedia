-- Prove2me | solution 1 for EthierKurtz.kmt_smoothed_conditional_quantile_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T02:26:42.530124+00:00
-- url     : https://prove2.me/submissions/8f9e9fc8-5dec-44b4-8b7c-18dab24d8da4

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_quantile_sandwich
import Theorems.Thm_EthierKurtz_smoothed_sum_density_product_ratio

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section P99Hyps
section X3_Lc4

/-! R4 / Q2 (rest): Gaussian smoothing and the local CLT for densities.
* `conv_gauss_eq`: `ν ∗ N(0,v)` has density `x ↦ ∫⁻ φ_v(x-y) dν`;
* `lint_dens`: that density as `ofReal` of a Bochner integral;
* `charFun_sumLaw`: characteristic function of an iid sum;
* `lclt_dens`: density of (iid sum of `H0`) ∗ `N(0,Nσ²)` is within `C/N + C(1-κ')^(N-1)/σ` of `φ_{N D2}`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma gaussianPDFReal_le_top (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v x ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  have : exp (-(x - 0) ^ 2 / (2 * v)) ≤ 1 := by
    rw [exp_le_one_iff]
    have : 0 ≤ (x - 0) ^ 2 / (2 * v) := by positivity
    rw [neg_div]; linarith
  calc (√(2 * π * v))⁻¹ * exp (-(x - 0) ^ 2 / (2 * v)) ≤ (√(2 * π * v))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

lemma integrable_pdf_shift (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) (x : ℝ) :
    Integrable (fun y => gaussianPDFReal 0 v (x - y)) ν := by
  refine (integrable_const ((√(2 * π * v))⁻¹)).mono'
    ((measurable_gaussianPDFReal 0 v).comp (measurable_const_sub x)).aestronglyMeasurable ?_
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact gaussianPDFReal_le_top v _

lemma lint_dens (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) (x : ℝ) :
    ∫⁻ y, gaussianPDF 0 v (x - y) ∂ν = ENNReal.ofReal (∫ y, gaussianPDFReal 0 v (x - y) ∂ν) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_pdf_shift ν v x)
    (Eventually.of_forall fun y => gaussianPDFReal_nonneg _ _ _)]
  rfl

lemma conv_gauss_eq (ν : Measure ℝ) [IsProbabilityMeasure ν] {v : ℝ≥0} (hv : v ≠ 0) :
    ν ∗ gaussianReal 0 v = volume.withDensity (fun x => ∫⁻ y, gaussianPDF 0 v (x - y) ∂ν) := by
  have hg : Measurable (gaussianPDF 0 v) := measurable_gaussianPDF 0 v
  have hg2 : Measurable (Function.uncurry fun (x y : ℝ) => gaussianPDF 0 v (x - y)) :=
    hg.comp (measurable_fst.sub measurable_snd)
  have hf : Measurable (fun x => ∫⁻ y, gaussianPDF 0 v (x - y) ∂ν) := hg2.lintegral_prod_right'
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [Measure.lintegral_conv hφ, gaussianReal_of_var_ne_zero 0 hv,
    lintegral_withDensity_eq_lintegral_mul _ hf hφ]
  have htr : ∀ y : ℝ, ∫⁻ z, φ (y + z) ∂(volume.withDensity (gaussianPDF 0 v))
      = ∫⁻ x, gaussianPDF 0 v (x - y) * φ x := by
    intro y
    have hφy : Measurable (fun z => φ (y + z)) := hφ.comp (measurable_const_add y)
    rw [lintegral_withDensity_eq_lintegral_mul _ hg hφy]
    have := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x => gaussianPDF 0 v (x - y) * φ x) y
    simp only [add_sub_cancel_right] at this
    rw [← this]
    congr 1
    funext z
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [add_comm]
  simp_rw [htr]
  rw [lintegral_lintegral_swap]
  · congr 1
    funext x
    show ∫⁻ y, gaussianPDF 0 v (x - y) * φ x ∂ν = (∫⁻ y, gaussianPDF 0 v (x - y) ∂ν) * φ x
    exact lintegral_mul_const _ (hg.comp (measurable_const_sub x))
  · exact ((hg.comp (measurable_snd.sub measurable_fst)).mul
      (hφ.comp measurable_snd)).aemeasurable

end P99bcb804

end X3_Lc4

section X4_Tl1

/-! R4 / Q3: Esscher tilt of the smoothed sum density, for laws with an exponential moment.
* `pi_wdE`, `com_int`: change of measure from `pi F` to `pi (F.tilted (t·))`;
* `sq_complete`: `φ_v(u) e^{tu} = e^{t²v/2} φ_v(u - tv)`;
* `tilt_dens`: `∫ φ_v(a-y) d(ΣF) = M(t)^N e^{t²v/2} e^{-ta} ∫ φ_v(a - tv - y) d(ΣF_t)`;
* `sum_center`: shifting every summand by `-c` shifts the sum law by `-N c`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Tl1

variable {ι : Type} [Fintype ι]

lemma pi_wdE (μ : Measure ℝ) [IsProbabilityMeasure μ] (ρ : ℝ → ℝ≥0∞) (hρ : Measurable ρ)
    [IsProbabilityMeasure (μ.withDensity ρ)] :
    Measure.pi (fun _ : ι => μ.withDensity ρ) =
      (Measure.pi fun _ : ι => μ).withDensity (fun x => ∏ i, ρ (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have e : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, ρ (x i)) =
      fun x => ∏ i, (s i).indicator ρ (x i) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_pi, mem_univ, true_implies, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → ℝ) => (s i).indicator ρ (x i))
    (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun i => (s i).indicator ρ)
      (fun i => (hρ.indicator (hs i)).aemeasurable))
    (fun i => (hρ.indicator (hs i)).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  exact (measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp (hρ.indicator (hs i))

/-- Change of measure to the tilted product law (integral form, any integrand). -/
lemma com_int (F : Measure ℝ) [IsProbabilityMeasure F] {t : ℝ}
    (hI : Integrable (fun x => exp (t * x)) F) (g : (ι → ℝ) → ℝ) :
    ∫ x, g x ∂(Measure.pi fun _ : ι => F) =
      ∫ x, mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (-(t * ∑ i, x i)) * g x
        ∂(Measure.pi fun _ : ι => F.tilted (fun x => t * x)) := by
  set M := mgf (fun y : ℝ => y) F t with hMdef
  have hM : 0 < M := mgf_pos hI
  set ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (t * x) / M) with hρdef
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (by fun_prop)
  have hFt : F.tilted (fun x => t * x) = F.withDensity ρ := rfl
  have : IsProbabilityMeasure (F.withDensity ρ) := hFt ▸ isProbabilityMeasure_tilted hI
  rw [hFt, pi_wdE F ρ hρ, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x : ι → ℝ => ∏ i, ρ (x i)) from
      Finset.measurable_prod _ fun i _ => hρ.comp (measurable_pi_apply i))
    (ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [smul_eq_mul, ENNReal.toReal_prod]
  simp only [hρdef, ENNReal.toReal_ofReal (div_pos (exp_pos _) hM).le]
  rw [Finset.prod_div_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
    ← Finset.mul_sum]
  have hMm : M ^ Fintype.card ι ≠ 0 := pow_ne_zero _ hM.ne'
  rw [← mul_assoc, ← mul_assoc, div_mul_eq_mul_div, mul_div_assoc, div_self hMm, mul_one,
    ← exp_add, add_neg_cancel, exp_zero, one_mul]

lemma sq_complete (v : ℝ≥0) (t u : ℝ) :
    gaussianPDFReal 0 v u * exp (t * u) = exp (t ^ 2 * v / 2) * gaussianPDFReal 0 v (u - t * v) := by
  by_cases hv : v = 0
  · subst hv; simp [gaussianPDFReal_zero_var]
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  simp only [gaussianPDFReal, sub_zero]
  rw [mul_assoc, ← exp_add, mul_left_comm, ← exp_add]
  congr 2
  field_simp
  ring

lemma tilt_dens (F : Measure ℝ) [IsProbabilityMeasure F] {t : ℝ}
    (hI : Integrable (fun x => exp (t * x)) F) (v : ℝ≥0) (a : ℝ) :
    ∫ y, gaussianPDFReal 0 v (a - y) ∂((Measure.pi fun _ : ι => F).map (fun p => ∑ i, p i))
      = mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (t ^ 2 * v / 2) * exp (-(t * a)) *
        ∫ y, gaussianPDFReal 0 v (a - t * v - y)
          ∂((Measure.pi fun _ : ι => F.tilted (fun x => t * x)).map (fun p => ∑ i, p i)) := by
  have hs : Measurable (fun p : ι → ℝ => ∑ i, p i) := by fun_prop
  have hg : ∀ b : ℝ, Measurable (fun y => gaussianPDFReal 0 v (b - y)) := fun b =>
    (measurable_gaussianPDFReal 0 v).comp (measurable_const_sub b)
  rw [integral_map hs.aemeasurable (hg a).aestronglyMeasurable,
    integral_map hs.aemeasurable (hg _).aestronglyMeasurable, com_int F hI, ← integral_const_mul]
  congr 1
  funext x
  have h := sq_complete v t (a - ∑ i, x i)
  have e : exp (-(t * ∑ i, x i)) = exp (-(t * a)) * exp (t * (a - ∑ i, x i)) := by
    rw [← exp_add]; congr 1; ring
  rw [e, show a - t * v - ∑ i, x i = a - ∑ i, x i - t * v by ring]
  calc mgf (fun y : ℝ => y) F t ^ Fintype.card ι * (exp (-(t * a)) * exp (t * (a - ∑ i, x i)))
        * gaussianPDFReal 0 v (a - ∑ i, x i)
      = mgf (fun y : ℝ => y) F t ^ Fintype.card ι * exp (-(t * a))
        * (gaussianPDFReal 0 v (a - ∑ i, x i) * exp (t * (a - ∑ i, x i))) := by ring
    _ = _ := by rw [h]; ring

end Tl1

end P99bcb804

end X4_Tl1

section X5_Cg1

/-! R4 / Q3: cumulants of a law with exponential moments (uniform local bounds).
* `taylor_an`: Taylor with Lagrange remainder for a function analytic on a neighbourhood;
* `itd_itd`: `iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (k + m) f`;
* `ioo_sub_int`, `an_cgf`, `V_zero`: the cgf `ψ` is analytic on `(-a0, a0)` and `ψ''(0) = 1`;
* `cum_local`: `∃ t1 B`, on `[-2t1, 2t1]`: `1/2 ≤ ψ'' ≤ 2`, `|ψ'''| ≤ B`;
* `cum_T0/T1/T2`: Taylor bounds of `ψ'', ψ', ψ` on `[-t1, t1]`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal Nat

namespace P99bcb804

lemma taylor_an {f : ℝ → ℝ} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    {x₀ x : ℝ} (hsub : uIcc x₀ x ⊆ U) (n : ℕ) {B : ℝ}
    (hB : ∀ y ∈ U, |iteratedDeriv (n + 1) f y| ≤ B) :
    |f x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / (k ! : ℝ)|
      ≤ B * |x - x₀| ^ (n + 1) / ((n + 1) ! : ℝ) := by
  rcases eq_or_ne x₀ x with h | h
  · subst h
    rw [Finset.sum_range_succ']
    simp
  have hu : UniqueDiffOn ℝ (uIcc x₀ x) := uniqueDiffOn_uIcc h
  have hcd : ContDiffOn ℝ (n + 1) f (uIcc x₀ x) := (hf.mono hsub).contDiffOn hu
  obtain ⟨x', hx', heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv h hcd
  have hx0 : x₀ ∈ uIcc x₀ x := left_mem_uIcc
  have e : taylorWithinEval f n (uIcc x₀ x) x₀ x
      = ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f x₀ * (x - x₀) ^ k / (k ! : ℝ) := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hu ((hf x₀ (hsub hx0)).contDiffAt) hx0, smul_eq_mul]
    ring
  rw [← e, heq, abs_div, abs_mul, abs_pow, Nat.abs_cast]
  gcongr
  exact hB x' (hsub (Set.uIoo_subset_uIcc_self hx'))

lemma itd_itd (f : ℝ → ℝ) (k m : ℕ) :
    iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (k + m) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    ← Function.iterate_add_apply]

section Cum

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma ioo_sub_int (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) :
    Ioo (-a0) a0 ⊆ interior (integrableExpSet (fun x : ℝ => x) G) :=
  interior_maximal (fun t ht => hexp t (abs_le.2 ⟨ht.1.le, ht.2.le⟩)) isOpen_Ioo

lemma an_cgf (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) (k : ℕ) :
    AnalyticOnNhd ℝ (iteratedDeriv k (cgf (fun x : ℝ => x) G)) (Ioo (-a0) a0) := by
  rw [iteratedDeriv_eq_iterate]
  exact (analyticOnNhd_cgf.mono (ioo_sub_int hexp)).iterated_deriv k

/-- Taylor bounds for the cgf `ψ` and its first two derivatives on `[-t1, t1]`. -/
lemma cum_taylor {t1 B : ℝ} (ht1 : 0 < t1) (h2a : 2 * t1 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {t s : ℝ} (ht : |t| ≤ t1) (hs : |s| ≤ t1) :
    |iteratedDeriv 2 (cgf (fun x : ℝ => x) G) s - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t|
        ≤ B * |s - t| ∧
    |iteratedDeriv 1 (cgf (fun x : ℝ => x) G) s - iteratedDeriv 1 (cgf (fun x : ℝ => x) G) t
        - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t)| ≤ B * |s - t| ^ 2 / 2 ∧
    |cgf (fun x : ℝ => x) G s - cgf (fun x : ℝ => x) G t
        - iteratedDeriv 1 (cgf (fun x : ℝ => x) G) t * (s - t)
        - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) ^ 2 / 2| ≤ B * |s - t| ^ 3 / 6 := by
  set ψ := cgf (fun x : ℝ => x) G with hψ
  set U := Ioo (-(2 * t1)) (2 * t1) with hU
  have hUa : U ⊆ Ioo (-a0) a0 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub : uIcc t s ⊆ U := by
    intro x hx
    rcases abs_le.1 ht with ⟨h1, h2⟩
    rcases abs_le.1 hs with ⟨h3, h4⟩
    rcases Set.mem_uIcc.1 hx with hx | hx <;>
      exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hB : ∀ (m n : ℕ), m + n = 2 → ∀ y ∈ U, |iteratedDeriv (n + 1) (iteratedDeriv m ψ) y| ≤ B := by
    intro m n hmn y hy
    rw [itd_itd, show n + 1 + m = 3 by omega]
    exact hW y ⟨hy.1.le, hy.2.le⟩
  have an : ∀ m : ℕ, AnalyticOnNhd ℝ (iteratedDeriv m ψ) U := fun m => (an_cgf hexp m).mono hUa
  refine ⟨?_, ?_, ?_⟩
  · have := taylor_an (an 2) hsub 0 (hB 2 0 rfl)
    simpa using this
  · have := taylor_an (an 1) hsub 1 (hB 1 1 rfl)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, itd_itd] at this
    simp [Nat.factorial] at this
    rw [sub_add_eq_sub_sub] at this
    simpa [iteratedDeriv_one] using this
  · have := taylor_an (an 0) hsub 2 (hB 0 2 rfl)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, itd_itd, iteratedDeriv_zero] at this
    have e : ∀ x : ℝ, x - (0 + ψ t * (s - t) ^ 0 / ((0 : ℕ)! : ℝ)
        + iteratedDeriv 1 ψ t * (s - t) ^ 1 / ((1 : ℕ)! : ℝ)
        + iteratedDeriv 2 ψ t * (s - t) ^ 2 / ((2 : ℕ)! : ℝ))
        = x - ψ t - iteratedDeriv 1 ψ t * (s - t) - iteratedDeriv 2 ψ t * (s - t) ^ 2 / 2 := by
      intro x; simp [Nat.factorial]; ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    simp [Nat.factorial]

end Cum

end P99bcb804

end X5_Cg1

section X7_Cg3

/-! R4 / Q3: hypotheses of `lclt_dens` for the centred tilted law `Hc G t`.
* `smooth_taylor`: Gaussian smoothing keeps a cubic Taylor bound of `charFun`;
* `Hc G t = (G.tilted (t·)).map (· - tmu G t)`: `Hc_prob`, `int_Hc`, `Hc_mean`, `Hc_var`;
* `Hc_m3`: uniform third absolute moment on `|t| ≤ t1`;
* `Hc_far`: `‖charFun (Hc G t) s · e^{-σ²s²/2}‖ ≤ 1 - (p/2)(1-e^{-v/2}) min(s²,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Hc

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- The tilted mean `ψ'(t)`. -/
noncomputable def tmu (G : Measure ℝ) (t : ℝ) : ℝ := deriv (cgf (fun x : ℝ => x) G) t

lemma mem_int_of (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| < a0) : t ∈ interior (integrableExpSet (fun x : ℝ => x) G) :=
  ioo_sub_int hexp ⟨by linarith [(abs_lt.1 ht).1], (abs_lt.1 ht).2⟩

end Hc

end P99bcb804

end X7_Cg3

section X11_Cr3

/-! R4 / Cr3: smoothed cumulant functions, saddle point, Legendre expansion.
`Ls G σ t = cgf t + t²σ²/2` (cgf of `G ∗ N(0,σ²)`), `L1s = Ls'`, `L2s = Ls''`.
* `L1s_mono`: `L1s` increases at rate `≥ 1/2` on `[-t1,t1]`; `saddle`: `L1s t = c` solvable for `|c| ≤ t1/2`, `|t| ≤ 2|c|`;
* `Ls_taylor`: Taylor bounds; `leg_at`: Legendre expansion of `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def Ls (G : Measure ℝ) (σ t : ℝ) : ℝ := cgf (fun x : ℝ => x) G t + t ^ 2 * σ ^ 2 / 2
noncomputable def L1s (G : Measure ℝ) (σ t : ℝ) : ℝ := tmu G t + t * σ ^ 2
noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma tmu_hasDeriv (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t : ℝ} (ht : |t| < a0) :
    HasDerivAt (tmu G) (iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t) t := by
  have h1 : tmu G = iteratedDeriv 1 (cgf (fun x : ℝ => x) G) := by
    funext s; rw [iteratedDeriv_one]; rfl
  have hmem : t ∈ Ioo (-a0) a0 := ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
  have hd := (an_cgf hexp 1 t hmem).differentiableAt
  have e : iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t
      = deriv (iteratedDeriv 1 (cgf (fun x : ℝ => x) G)) t :=
    congrFun (iteratedDeriv_succ (n := 1)) t
  rw [h1, e]
  exact hd.hasDerivAt

lemma tmu_zero (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) : tmu G 0 = 0 := by
  rw [tmu, deriv_cgf_zero (mem_int_of hexp (by simpa using ha0))]
  simp [hm]

lemma L1s_hasDeriv (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (σ : ℝ) {t : ℝ} (ht : |t| < a0) : HasDerivAt (L1s G σ) (L2s G σ t) t := by
  have h := (tmu_hasDeriv hexp ht).add ((hasDerivAt_id' t).mul_const (σ ^ 2))
  have e : L1s G σ = fun s => tmu G s + s * σ ^ 2 := rfl
  rw [e, L2s]
  exact h.congr_deriv (by ring)

lemma L1s_mono (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {s t : ℝ} (hs : |s| ≤ t1) (ht : |t| ≤ t1) (hst : s ≤ t) :
    (t - s) / 2 ≤ L1s G σ t - L1s G σ s := by
  have hder : ∀ u, |u| ≤ t1 → HasDerivAt (L1s G σ) (L2s G σ u) u := fun u hu =>
    L1s_hasDeriv hexp σ (by linarith)
  have hcont : ContinuousOn (L1s G σ) (Icc (-t1) t1) := fun u hu =>
    (hder u (abs_le.2 hu)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (L1s G σ) (interior (Icc (-t1) t1)) := fun u hu =>
    (hder u (abs_le.2 (mem_Icc.1 (interior_subset hu)))).differentiableAt.differentiableWithinAt
  have hge : ∀ x ∈ interior (Icc (-t1) t1), 1 / 2 ≤ deriv (L1s G σ) x := by
    intro x hx
    have hx' : |x| ≤ t1 := abs_le.2 (mem_Icc.1 (interior_subset hx))
    rw [(hder x hx').deriv, L2s]
    have := (hV x hx').1
    linarith [sq_nonneg σ]
  have := (convex_Icc (-t1) t1).mul_sub_le_image_sub_of_le_deriv hcont hdiff hge s (abs_le.1 hs)
    t (abs_le.1 ht) hst
  linarith

lemma L1s_low (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {s t : ℝ} (hs : |s| ≤ t1) (ht : |t| ≤ t1) :
    |s - t| ≤ 2 * |L1s G σ s - L1s G σ t| := by
  rcases le_total s t with hst | hst
  · have := L1s_mono hexp h2 ht1 hV σ hs ht hst
    rw [abs_sub_comm s t, abs_of_nonneg (by linarith), abs_sub_comm]
    have := le_abs_self (L1s G σ t - L1s G σ s)
    linarith
  · have := L1s_mono hexp h2 ht1 hV σ ht hs hst
    rw [abs_of_nonneg (by linarith)]
    have := le_abs_self (L1s G σ s - L1s G σ t)
    linarith

lemma saddle (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ)
    {c : ℝ} (hc : |c| ≤ t1 / 2) :
    ∃ t, |t| ≤ t1 ∧ L1s G σ t = c ∧ |t| ≤ 2 * |c| := by
  have h0 : L1s G σ 0 = 0 := by simp [L1s, tmu_zero ha0 hexp hm]
  have hz : |(0 : ℝ)| ≤ t1 := by simp [ht1.le]
  have ht1a : |t1| ≤ t1 := by rw [abs_of_pos ht1]
  have ht1b : |-t1| ≤ t1 := by rw [abs_neg, abs_of_pos ht1]
  have hup := L1s_mono hexp h2 ht1 hV σ hz ht1a ht1.le
  have hlo := L1s_mono hexp h2 ht1 hV σ ht1b hz (by linarith)
  have hcont : ContinuousOn (L1s G σ) (Icc (-t1) t1) := fun u hu =>
    (L1s_hasDeriv hexp σ (by have := abs_le.2 hu; linarith)).continuousAt.continuousWithinAt
  have hmem : c ∈ Icc (L1s G σ (-t1)) (L1s G σ t1) := by
    have := abs_le.1 hc
    constructor <;> linarith
  obtain ⟨t, htI, htc⟩ := intermediate_value_Icc (by linarith) hcont hmem
  have ht : |t| ≤ t1 := abs_le.2 htI
  refine ⟨t, ht, htc, ?_⟩
  have := L1s_low hexp h2 ht1 hV σ ht hz
  rwa [sub_zero, htc, h0, sub_zero] at this

lemma Ls_taylor (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (σ : ℝ) {t s : ℝ} (ht : |t| ≤ t1) (hs : |s| ≤ t1) :
    |L1s G σ s - L1s G σ t - L2s G σ t * (s - t)| ≤ B * |s - t| ^ 2 / 2 ∧
    |Ls G σ s - Ls G σ t - L1s G σ t * (s - t) - L2s G σ t * (s - t) ^ 2 / 2|
      ≤ B * |s - t| ^ 3 / 6 := by
  obtain ⟨-, hb1, hb0⟩ := cum_taylor ht1 h2 hexp hW ht hs
  rw [iteratedDeriv_one] at hb1 hb0
  constructor
  · have e : L1s G σ s - L1s G σ t - L2s G σ t * (s - t)
        = deriv (cgf (fun x : ℝ => x) G) s - deriv (cgf (fun x : ℝ => x) G) t
          - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) := by
      simp only [L1s, L2s, tmu]; ring
    rw [e]; exact hb1
  · have e : Ls G σ s - Ls G σ t - L1s G σ t * (s - t) - L2s G σ t * (s - t) ^ 2 / 2
        = cgf (fun x : ℝ => x) G s - cgf (fun x : ℝ => x) G t
          - deriv (cgf (fun x : ℝ => x) G) t * (s - t)
          - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t * (s - t) ^ 2 / 2 := by
      simp only [Ls, L1s, L2s, tmu]; ring
    rw [e]; exact hb0

end Cr3

end P99bcb804

end X11_Cr3

section X12_Cr4

/-! R4 / Cr4: local Cramér form of the smoothed iid-sum density at the saddle point.
`lc_at`: `f(N L1s t) = exp(-N Λ(t)) (φ_{N L2s t}(0) ± (C/N + C(1-κ')^{N-1}/σ))`, `Λ(t) = t L1s t - Ls t`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Cr4

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma mgf_pow_exp (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t : ℝ} (ht : |t| ≤ a0) (N : ℕ) (σ a : ℝ) :
    mgf (fun x : ℝ => x) G t ^ N * exp (t ^ 2 * (N * σ ^ 2) / 2) * exp (-(t * a))
      = exp (N * Ls G σ t - t * a) := by
  rw [← exp_cgf (hexp t ht), ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Ls]
  congr 1
  ring

end Cr4

end P99bcb804

end X12_Cr4

section X13_Nd1

/-! R4 / Nd1 (Q5 node, near region): ratio of the smoothed density at `N(c±δ)` to `N c`.
`near_ratio`: `f(N(c+δ)) f(N(c-δ)) = f(Nc)² exp(-Nδ²/L2s tc) exp(±K(1/√N + |δ| + N|δ|³))`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

/-- density of the smoothed iid sum `Σ_ι G + N(0, card·σ²)` at `a`. -/
noncomputable def fS (G : Measure ℝ) (ι : Type) [Fintype ι] (σ a : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
    ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))

section Nd1

end Nd1

end P99bcb804

end X13_Nd1

section X14_Nd2

/-! R4 / Nd2: `near_ratio` (Q5 node, near region, pointwise). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd2

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem near_ratio :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (0 : ℝ) < a0 →
        (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
          ∫ (x : ℝ), x ∂G = (0 : ℝ) →
            ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
              (0 : ℝ) < p →
                p ≤ (1 : ℝ) →
                  (0 : NNReal) < v →
                    G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                      ∀ {t1 B : ℝ},
                        (0 : ℝ) < t1 →
                          (2 : ℝ) * t1 < a0 →
                            (0 : ℝ) ≤ B →
                              (∀ (t : ℝ),
                                  |t| ≤ t1 →
                                    (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                      iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                                (∀ t ∈ Set.Icc (-((2 : ℝ) * t1)) ((2 : ℝ) * t1),
                                    |iteratedDeriv (3 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t| ≤ B) →
                                  (∀ (t : ℝ),
                                      |t| ≤ t1 →
                                        (1 / 2 : ℝ) ≤
                                          ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                            ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                                    ∃ (κ' : ℝ) (K : ℝ) (N1 : ℝ),
                                      (0 : ℝ) < κ' ∧
                                        κ' ≤ (1 : ℝ) ∧
                                          (0 : ℝ) ≤ K ∧
                                            ∀ (ι : Type) [inst : Fintype ι] (σ c δ tc : ℝ),
                                              (0 : ℝ) < σ →
                                                σ ≤ (1 : ℝ) →
                                                  N1 ≤ ↑(Fintype.card ι) →
                                                    (2 : ℕ) ≤ Fintype.card ι →
                                                      ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ ≤
                                                          (1 : ℝ) / ↑(Fintype.card ι) →
                                                        |c| ≤ t1 / (4 : ℝ) →
                                                          |δ| ≤ t1 / (4 : ℝ) →
                                                            |tc| ≤ t1 →
                                                              P99bcb804.L1s G σ tc = c →
                                                                (0 : ℝ) < P99bcb804.fS G ι σ (↑(Fintype.card ι) * c) ∧
                                                                  Real.exp
                                                                            (-(↑(Fintype.card ι) *
                                                                                (tc * c - P99bcb804.Ls G σ tc))) *
                                                                          ((√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                            (√(P99bcb804.L2s G σ tc))⁻¹) *
                                                                        Real.exp (-1 : ℝ) ≤
                                                                      P99bcb804.fS G ι σ (↑(Fintype.card ι) * c) ∧
                                                                    P99bcb804.fS G ι σ (↑(Fintype.card ι) * (c + δ)) *
                                                                          P99bcb804.fS G ι σ (↑(Fintype.card ι) * (c - δ)) ≤
                                                                        P99bcb804.fS G ι σ (↑(Fintype.card ι) * c) ^
                                                                              (2 : ℕ) *
                                                                            Real.exp
                                                                              (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                                  P99bcb804.L2s G σ tc)) *
                                                                          Real.exp
                                                                            (K *
                                                                              ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                                ↑(Fintype.card ι) * |δ| ^ (3 : ℕ))) ∧
                                                                      P99bcb804.fS G ι σ (↑(Fintype.card ι) * c) ^ (2 : ℕ) *
                                                                            Real.exp
                                                                              (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                                  P99bcb804.L2s G σ tc)) *
                                                                          Real.exp
                                                                            (-(K *
                                                                                ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                                  ↑(Fintype.card ι) * |δ| ^ (3 : ℕ)))) ≤
                                                                        P99bcb804.fS G ι σ (↑(Fintype.card ι) * (c + δ)) *
                                                                          P99bcb804.fS G ι σ (↑(Fintype.card ι) * (c - δ)) := EthierKurtz.smoothed_sum_density_product_ratio

end Nd2

end P99bcb804

end X14_Nd2

section X16_Nd3

/-! R4 / Nd3: basic facts on the smoothed density `fS`: nonneg, bounded, measurable, a probability
density, and the Chernoff bound `fS a ≤ exp(N Ls t - t a) / √(2π N σ²)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd3

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma sumLaw_prob (H : Measure ℝ) [IsProbabilityMeasure H] (ι : Type) [Fintype ι] :
    IsProbabilityMeasure ((Measure.pi fun _ : ι => H).map (fun p => ∑ i, p i)) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma fS_nonneg (ι : Type) [Fintype ι] (σ a : ℝ) : 0 ≤ fS G ι σ a :=
  integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _

lemma int_pdf_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (v : ℝ≥0) (b : ℝ) :
    ∫ y, gaussianPDFReal 0 v (b - y) ∂ν ≤ (√(2 * π * v))⁻¹ := by
  calc ∫ y, gaussianPDFReal 0 v (b - y) ∂ν ≤ ∫ _y, (√(2 * π * v))⁻¹ ∂ν :=
        integral_mono (integrable_pdf_shift ν v b) (integrable_const _)
          fun y => gaussianPDFReal_le_top v (b - y)
    _ = (√(2 * π * v))⁻¹ := by simp

lemma fS_le (ι : Type) [Fintype ι] (σ a : ℝ) :
    fS G ι σ a ≤ (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹ := by
  haveI := sumLaw_prob G ι
  have h := int_pdf_le ((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))
    (Fintype.card ι * σ ^ 2).toNNReal a
  rwa [Real.coe_toNNReal _ (by positivity)] at h

lemma fS_eq (ι : Type) [Fintype ι] (σ : ℝ) :
    fS G ι σ = fun a => (∫⁻ y, gaussianPDF 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
      ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))).toReal := by
  haveI := sumLaw_prob G ι
  funext a
  rw [lint_dens, ENNReal.toReal_ofReal (integral_nonneg fun _ => gaussianPDFReal_nonneg _ _ _)]
  rfl

lemma fS_meas_l (ι : Type) [Fintype ι] (σ : ℝ) :
    Measurable (fun a => ∫⁻ y, gaussianPDF 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
      ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i))) := by
  have hg : Measurable (gaussianPDF 0 (Fintype.card ι * σ ^ 2).toNNReal) :=
    measurable_gaussianPDF _ _
  have hg2 : Measurable (Function.uncurry fun (x y : ℝ) =>
      gaussianPDF 0 (Fintype.card ι * σ ^ 2).toNNReal (x - y)) :=
    hg.comp (measurable_fst.sub measurable_snd)
  exact hg2.lintegral_prod_right'

lemma fS_meas (ι : Type) [Fintype ι] (σ : ℝ) : Measurable (fS G ι σ) := by
  rw [fS_eq]; exact (fS_meas_l ι σ).ennreal_toReal

lemma fS_lint (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    ∫⁻ a, ∫⁻ y, gaussianPDF 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y)
      ∂((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i)) = 1 := by
  haveI := sumLaw_prob G ι
  have hv : (Fintype.card ι * σ ^ 2).toNNReal ≠ 0 := by
    have : 0 < (Fintype.card ι : ℝ) * σ ^ 2 := by
      have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
      positivity
    exact (Real.toNNReal_pos.2 this).ne'
  have h := conv_gauss_eq ((Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i)) hv
  have h1 := congrArg (fun μ : Measure ℝ => μ univ) h
  simp only [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  exact h1.symm

lemma fS_integrable (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    Integrable (fS G ι σ) ∧ ∫ a, fS G ι σ a = 1 := by
  rw [fS_eq]
  refine ⟨integrable_toReal_of_lintegral_ne_top (fS_meas_l ι σ).aemeasurable
    (by rw [fS_lint ι hσ hN]; simp), ?_⟩
  rw [integral_toReal (fS_meas_l ι σ).aemeasurable, fS_lint ι hσ hN]
  · simp
  · refine Eventually.of_forall fun a => ?_
    haveI := sumLaw_prob G ι
    rw [lint_dens]; exact ENNReal.ofReal_lt_top

lemma fS_chernoff {a0 : ℝ} (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (ι : Type) [Fintype ι] (σ : ℝ) {t : ℝ} (ht : |t| ≤ a0) (a : ℝ) :
    fS G ι σ a ≤ exp (Fintype.card ι * Ls G σ t - t * a) *
      (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹ := by
  have hI := hexp t ht
  haveI : IsProbabilityMeasure (G.tilted (fun x => t * x)) := isProbabilityMeasure_tilted hI
  haveI := sumLaw_prob (G.tilted (fun x => t * x)) ι
  have hv : (((Fintype.card ι * σ ^ 2).toNNReal : ℝ≥0) : ℝ) = Fintype.card ι * σ ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  unfold fS
  rw [tilt_dens G hI, hv, ← mgf_pow_exp hexp ht (Fintype.card ι) σ a]
  have hb := int_pdf_le ((Measure.pi fun _ : ι => G.tilted (fun x => t * x)).map
    (fun p => ∑ i, p i)) (Fintype.card ι * σ ^ 2).toNNReal (a - t * (Fintype.card ι * σ ^ 2))
  rw [hv] at hb
  have hpos : 0 ≤ mgf (fun y : ℝ => y) G t ^ Fintype.card ι * exp (t ^ 2 * (Fintype.card ι * σ ^ 2) / 2)
      * exp (-(t * a)) := by
    have : 0 ≤ mgf (fun y : ℝ => y) G t := mgf_nonneg
    positivity
  exact mul_le_mul_of_nonneg_left hb hpos

end Nd3

end P99bcb804

end X16_Nd3

section X18_Nd4

/-! R4 / Nd4 (Q5 node, far region): `far_exp` (∫ of e^{-a|x|} off [-r,r]), `kappa_cond`
(`σ⁻¹ ≤ e^{κN/2}` gives the LCLT error condition), `far_pt` (two-sided Chernoff bound for the
product `fS(Nc + d/2) fS(Nc - d/2)`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd4

lemma far_exp {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    IntegrableOn (fun x : ℝ => exp (-(a * |x|))) (Iic (-r) ∪ Ioi r) ∧
    ∫ x in Iic (-r) ∪ Ioi r, exp (-(a * |x|)) = 2 * exp (-(a * r)) / a := by
  have e1 : EqOn (fun x : ℝ => exp (-(a * |x|))) (fun x => exp (a * x)) (Iic (-r)) := by
    intro x hx
    simp only
    rw [abs_of_nonpos (by linarith [mem_Iic.1 hx])]
    congr 1; ring
  have e2 : EqOn (fun x : ℝ => exp (-(a * |x|))) (fun x => exp ((-a) * x)) (Ioi r) := by
    intro x hx
    simp only
    rw [abs_of_pos (by linarith [mem_Ioi.1 hx])]
    congr 1; ring
  have i1 : IntegrableOn (fun x : ℝ => exp (-(a * |x|))) (Iic (-r)) :=
    (integrableOn_exp_mul_Iic ha (-r)).congr_fun e1.symm measurableSet_Iic
  have i2 : IntegrableOn (fun x : ℝ => exp (-(a * |x|))) (Ioi r) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) r).congr_fun e2.symm measurableSet_Ioi
  have hd : Disjoint (Iic (-r)) (Ioi r) :=
    Set.disjoint_left.2 fun x h1 h2 => by linarith [mem_Iic.1 h1, mem_Ioi.1 h2]
  refine ⟨i1.union i2, ?_⟩
  rw [setIntegral_union hd measurableSet_Ioi i1 i2, setIntegral_congr_fun measurableSet_Iic e1,
    setIntegral_congr_fun measurableSet_Ioi e2, integral_exp_mul_Iic ha,
    integral_exp_mul_Ioi (neg_neg_of_pos ha), show a * -r = -(a * r) by ring,
    show -a * r = -(a * r) by ring]
  field_simp
  ring

lemma kappa_cond {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (n : ℕ) (hn8 : 8 * exp κ / κ ^ 2 ≤ n)
    (hn2 : 2 ≤ n) (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ⁻¹ ≤ exp (κ / 2 * n)) :
    (1 - κ) ^ (n - 1) / σ ≤ 1 / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h1 : (1 - κ) ^ (n - 1) ≤ exp (-(κ * ((n : ℝ) - 1))) := by
    calc (1 - κ) ^ (n - 1) ≤ exp (-κ) ^ (n - 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith [add_one_le_exp (-κ)]) _
      _ = exp (-(κ * ((n : ℝ) - 1))) := by
          rw [← exp_nat_mul]; congr 1
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; ring
  have h2 : (n : ℝ) * exp κ ≤ exp (κ / 2 * n) := by
    have q := quadratic_le_exp_of_nonneg (x := κ / 2 * n) (by positivity)
    have h3 : exp κ ≤ κ ^ 2 * n / 8 := by
      rw [div_le_iff₀ (by positivity)] at hn8
      linarith
    nlinarith [exp_pos κ]
  rw [div_eq_mul_inv]
  calc (1 - κ) ^ (n - 1) * σ⁻¹ ≤ exp (-(κ * ((n : ℝ) - 1))) * exp (κ / 2 * n) :=
        mul_le_mul h1 hσ (inv_pos.2 hσ0).le (exp_pos _).le
    _ = exp κ / exp (κ / 2 * n) := by
        rw [← exp_add, ← exp_sub]; congr 1; ring
    _ ≤ 1 / n := by
        rw [div_le_div_iff₀ (exp_pos _) hn]; linarith [h2]

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma far_pt (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (ι : Type) [Fintype ι] {σ c tc u : ℝ} (hσ1 : σ ≤ 1) (hσ0 : 0 < σ) (htc : |tc| ≤ t1 / 2)
    (hu0 : 0 ≤ u) (hu : u ≤ t1 / 2) (hLc : L1s G σ tc = c) (d : ℝ) :
    fS G ι σ (Fintype.card ι * c + d / 2) * fS G ι σ (Fintype.card ι * c - d / 2)
      ≤ exp (-(2 * (Fintype.card ι * (tc * c - Ls G σ tc)))) *
          exp (Fintype.card ι * ((3 + B * t1) * u ^ 2) - u * |d|) *
          (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹ ^ 2 := by
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hN0 : 0 ≤ N := by positivity
  set v : ℝ := if 0 ≤ d then u else -u with hv
  have hva : |v| = u := by
    rw [hv]; split_ifs
    · exact abs_of_nonneg hu0
    · rw [abs_neg]; exact abs_of_nonneg hu0
  have hvd : v * d = u * |d| := by
    rw [hv]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have htp : |tc + v| ≤ t1 := by
    calc |tc + v| ≤ |tc| + |v| := abs_add_le _ _
      _ ≤ t1 := by rw [hva]; linarith
  have htm : |tc - v| ≤ t1 := by
    calc |tc - v| ≤ |tc| + |v| := abs_sub _ _
      _ ≤ t1 := by rw [hva]; linarith
  have htc' : |tc| ≤ t1 := by linarith
  have hp := fS_chernoff hexp ι σ (t := tc + v) (by linarith) (N * c + d / 2)
  have hm := fS_chernoff hexp ι σ (t := tc - v) (by linarith) (N * c - d / 2)
  have Tp := (Ls_taylor hexp ht1 h2 hW σ htc' htp).2
  have Tm := (Ls_taylor hexp ht1 h2 hW σ htc' htm).2
  rw [show tc + v - tc = v by ring] at Tp
  rw [show tc - v - tc = -v by ring, abs_neg, neg_sq] at Tm
  have hL2 : L2s G σ tc ≤ 3 := by
    have := (hV tc htc').2
    have : σ ^ 2 ≤ 1 := by nlinarith
    simp only [L2s]; linarith
  have hL20 : 0 ≤ L2s G σ tc := by
    have := (hV tc htc').1
    simp only [L2s]; linarith [sq_nonneg σ]
  have hcube : B * |v| ^ 3 / 6 ≤ B * t1 * u ^ 2 / 2 := by
    rw [hva]
    have h3 : u ^ 3 ≤ t1 * u ^ 2 := by nlinarith [sq_nonneg u]
    linarith [mul_le_mul_of_nonneg_left h3 hB, mul_nonneg (mul_nonneg hB ht1.le) (sq_nonneg u)]
  have hsum : Ls G σ (tc + v) + Ls G σ (tc - v) ≤ 2 * Ls G σ tc + (3 + B * t1) * u ^ 2 := by
    have a1 := (abs_le.1 Tp).2
    have a2 := (abs_le.1 Tm).2
    have hv2 : v ^ 2 = u ^ 2 := by rw [← sq_abs, hva]
    have : L2s G σ tc * v ^ 2 ≤ 3 * u ^ 2 := by rw [hv2]; nlinarith [sq_nonneg u]
    linarith
  have hq0 : 0 ≤ (√(2 * π * (N * σ ^ 2)))⁻¹ := by positivity
  calc fS G ι σ (N * c + d / 2) * fS G ι σ (N * c - d / 2)
      ≤ (exp (N * Ls G σ (tc + v) - (tc + v) * (N * c + d / 2)) * (√(2 * π * (N * σ ^ 2)))⁻¹) *
        (exp (N * Ls G σ (tc - v) - (tc - v) * (N * c - d / 2)) * (√(2 * π * (N * σ ^ 2)))⁻¹) :=
        mul_le_mul hp hm (fS_nonneg ι σ _) (by positivity)
    _ = exp (N * (Ls G σ (tc + v) + Ls G σ (tc - v)) - 2 * N * c * tc - v * d) *
          (√(2 * π * (N * σ ^ 2)))⁻¹ ^ 2 := by
        have e : ∀ A A' q : ℝ, (A * q) * (A' * q) = (A * A') * q ^ 2 := by intros; ring
        rw [e, ← exp_add]; congr 2; ring
    _ ≤ exp (-(2 * (N * (tc * c - Ls G σ tc)))) * exp (N * ((3 + B * t1) * u ^ 2) - u * |d|) *
          (√(2 * π * (N * σ ^ 2)))⁻¹ ^ 2 := by
        rw [← exp_add, hvd]
        gcongr
        linarith [mul_le_mul_of_nonneg_left hsum hN0]

end Nd4

end P99bcb804

end X18_Nd4

section X19_Mills

/-! Gaussian toolkit for 99bcb804 (KMT): standard normal density, cdf, Mills-ratio bounds. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

/-- Standard normal density. -/
noncomputable def phi (t : ℝ) : ℝ := (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2))

lemma phi_pos (t : ℝ) : 0 < phi t := by
  unfold phi; positivity

lemma gaussianPDFReal_std (t : ℝ) : gaussianPDFReal 0 1 t = phi t := by
  simp [gaussianPDFReal_def, phi, neg_div]

lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

lemma integrable_phi : Integrable phi := by
  have := integrable_gaussianPDFReal 0 1
  simpa [funext gaussianPDFReal_std] using this

/-- Standard normal cdf as an integral of the density. -/
lemma cdf_std_eq (x : ℝ) : cdf (gaussianReal 0 1) x = ∫ t in Iic x, phi t := by
  rw [cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic
      (fun t _ => gaussianPDFReal_nonneg _ _ t))]
  simp [gaussianPDFReal_std]

lemma integral_phi : ∫ t, phi t = 1 := by
  have := integral_gaussianPDFReal_eq_one 0 (v := 1) one_ne_zero
  simpa [funext gaussianPDFReal_std] using this

/-- Upper tail of the standard normal. -/
lemma one_sub_cdf_std (x : ℝ) : 1 - cdf (gaussianReal 0 1) x = ∫ t in Ioi x, phi t := by
  rw [cdf_std_eq, ← integral_phi, ← integral_add_compl (measurableSet_Iic (a := x)) integrable_phi,
    compl_Iic]
  ring

lemma phi_neg (t : ℝ) : phi (-t) = phi t := by
  simp [phi]

/-- The standard normal cdf has derivative `φ`. -/
lemma hasDerivAt_cdf_std (x : ℝ) :
    HasDerivAt (fun y => cdf (gaussianReal 0 1) y) (phi x) x := by
  have e : (fun y => cdf (gaussianReal 0 1) y)
      = fun y => (∫ t in Iic 0, phi t) + ∫ t in (0 : ℝ)..y, phi t := by
    funext y
    rw [cdf_std_eq, ← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn
      integrable_phi.integrableOn]
    ring
  rw [e]
  exact ((continuous_phi.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_std_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq, one_sub_cdf_std]
  have : ∫ t in Iic (-x), phi t = ∫ t in Iic (-x), phi (-t) := by
    simp_rw [phi_neg]
  rw [this, integral_comp_neg_Iic, neg_neg]

lemma cdf_std_pos (x : ℝ) : 0 < cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq]
  have hsupp : Function.support phi = univ := by
    ext t; simp [(phi_pos t).ne']
  have hpos : 0 < volume (Function.support phi ∩ Iic x) := by
    rw [hsupp, univ_inter, Real.volume_Iic]; exact ENNReal.zero_lt_top
  exact (setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun t => (phi_pos t).le)
    integrable_phi.integrableOn).mpr hpos

lemma cdf_std_lt_one (x : ℝ) : cdf (gaussianReal 0 1) x < 1 := by
  have := cdf_std_pos (-x)
  rw [cdf_std_neg] at this
  linarith

/-! ### Stein solution for the indicator `1{w ≤ z}` (Chen–Goldstein–Shao, Lemma 2.3) -/

/-- Standard normal cdf as a real function. -/
noncomputable def Phi (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

/-! ## Child C (Tusnády quantile inequality), generic over the family of sum laws. -/

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := hasDerivAt_cdf_std x

/-! ## Gaussian hazard `Hz = φ/(1-Φ)` and the two-sided log-tail Taylor bound (KMT 1976 II, (4.5)). -/

end P99bcb804

end X19_Mills

section X22_DtC

/-! R4 / DtC: density -> normalisation `|K0 - 1| ≤ C3 ε` and L¹ closeness `∫|h - φ| ≤ C4 ε`
for a probability density `h` that is `K0 φ e^{±R}` on `|x| ≤ ε0/ε` (R = c0 ε (1+|x|³)) with tiny far mass. -/

open MeasureTheory Real Set Filter

namespace P99bcb804

/-- Hypothesis bundle for the density -> Tusnady chain. -/
def DtHyp (c0 ε0 A b : ℝ) (h : ℝ → ℝ) (K0 ε : ℝ) : Prop :=
  0 < ε ∧ 0 < K0 ∧ (∀ x, 0 ≤ h x) ∧ Integrable h ∧ ∫ x, h x = 1 ∧
  (∀ x, |x| ≤ ε0 / ε → h x ≤ K0 * phi x * exp (c0 * ε * (1 + |x| ^ 3))) ∧
  (∀ x, |x| ≤ ε0 / ε → K0 * phi x * exp (-(c0 * ε * (1 + |x| ^ 3))) ≤ h x) ∧
  ∫ x in (Icc (-(ε0 / ε)) (ε0 / ε))ᶜ, h x ≤ A * exp (-(b / ε ^ 2))

end P99bcb804

end X22_DtC

section X23_Nd5

/-! R4 / Nd5: the standardised conditional density of the half-difference given the total.
`ffN x = fS(Nc + s x/2) fS(Nc - s x/2)`, `s = √(2N L2s tc)`, `hN = ffN / ZN`. Integrability,
`near_x` (near bounds in the `x` variable) and `ZN_low` (`ZN ≥ 2 fS(Nc)² e^{-1}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ tc : ℝ) : ℝ :=
  √(2 * Fintype.card ι * L2s G σ tc)

noncomputable def ffN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  fS G ι σ (Fintype.card ι * c + sN G ι σ tc * x / 2) *
    fS G ι σ (Fintype.card ι * c - sN G ι σ tc * x / 2)

noncomputable def ZN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc : ℝ) : ℝ :=
  ∫ x, ffN G ι σ c tc x

noncomputable def hN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc x : ℝ) : ℝ :=
  ffN G ι σ c tc x / ZN G ι σ c tc

section Nd5

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma ffN_nonneg (ι : Type) [Fintype ι] (σ c tc x : ℝ) : 0 ≤ ffN G ι σ c tc x :=
  mul_nonneg (fS_nonneg _ _ _) (fS_nonneg _ _ _)

lemma ffN_meas (ι : Type) [Fintype ι] (σ c tc : ℝ) : Measurable (ffN G ι σ c tc) := by
  unfold ffN
  exact ((fS_meas ι σ).comp (by fun_prop)).mul ((fS_meas ι σ).comp (by fun_prop))

lemma fS_aff_int (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι)
    (a k : ℝ) (hk : k ≠ 0) : Integrable (fun x => fS G ι σ (a + k * x)) := by
  have h1 : Integrable (fun y => fS G ι σ (y + a)) := (fS_integrable ι hσ hN).1.comp_add_right a
  have h2 := h1.comp_mul_left' hk
  refine h2.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [add_comm]

lemma ffN_int (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) (c tc : ℝ)
    (hs : sN G ι σ tc ≠ 0) : Integrable (ffN G ι σ c tc) := by
  have hb := fS_aff_int (G := G) ι hσ hN (Fintype.card ι * c) (sN G ι σ tc / 2)
    (div_ne_zero hs two_ne_zero)
  refine (hb.const_mul (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹).mono'
    (ffN_meas ι σ c tc).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ffN_nonneg ι σ c tc x)]
  unfold ffN
  rw [show (Fintype.card ι : ℝ) * c + sN G ι σ tc * x / 2
      = Fintype.card ι * c + sN G ι σ tc / 2 * x by ring, mul_comm]
  exact mul_le_mul_of_nonneg_right (fS_le ι σ _) (fS_nonneg ι σ _)

set_option maxHeartbeats 1000000 in
lemma near_x {K t1 ε0 : ℝ} (hK : 0 ≤ K) (ι : Type) [Fintype ι] {σ c tc : ℝ}
    (hN : 0 < (Fintype.card ι : ℝ)) (hL1 : 1 / 2 ≤ L2s G σ tc) (hL3 : L2s G σ tc ≤ 3)
    (hε0 : ε0 ≤ t1 / 8)
    (H : ∀ δ : ℝ, |δ| ≤ t1 / 4 →
      fS G ι σ (Fintype.card ι * (c + δ)) * fS G ι σ (Fintype.card ι * (c - δ))
          ≤ fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(Fintype.card ι * δ ^ 2 / L2s G σ tc)) *
            exp (K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)) ∧
        fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(Fintype.card ι * δ ^ 2 / L2s G σ tc)) *
            exp (-(K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)))
          ≤ fS G ι σ (Fintype.card ι * (c + δ)) * fS G ι σ (Fintype.card ι * (c - δ)))
    (x : ℝ) (hx : |x| ≤ ε0 * √(2 * (Fintype.card ι : ℝ))) :
    ffN G ι σ c tc x ≤ fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(x ^ 2 / 2)) *
        exp (6 * K * (1 / √(2 * (Fintype.card ι : ℝ))) * (1 + |x| ^ 3)) ∧
      fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(x ^ 2 / 2)) *
        exp (-(6 * K * (1 / √(2 * (Fintype.card ι : ℝ))) * (1 + |x| ^ 3))) ≤ ffN G ι σ c tc x := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  set w := √(2 * N) with hwdef
  set l := √(L2s G σ tc) with hldef
  have hw : 0 < w := Real.sqrt_pos.2 (by positivity)
  have hw2 : w ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hl : 0 < l := Real.sqrt_pos.2 (by linarith)
  have hl2 : l ^ 2 = L2s G σ tc := Real.sq_sqrt (by linarith)
  have hl2' : l ≤ 2 := by nlinarith
  have hs : sN G ι σ tc = w * l := by
    rw [sN, ← hNdef, Real.sqrt_mul (by positivity)]
  set δ := l * x / w with hδdef
  have hNw : N = w ^ 2 / 2 := by rw [hw2]; ring
  have e1 : N * (c + δ) = N * c + sN G ι σ tc * x / 2 := by
    rw [hs, hδdef, hNw]; field_simp
  have e2 : N * (c - δ) = N * c - sN G ι σ tc * x / 2 := by
    rw [hs, hδdef, hNw]; field_simp
  have e3 : N * δ ^ 2 / L2s G σ tc = x ^ 2 / 2 := by
    rw [hδdef, ← hl2]; field_simp; rw [hw2]; ring
  have habs : |δ| = l * |x| * (1 / w) := by
    rw [hδdef, abs_div, abs_mul, abs_of_pos hl, abs_of_pos hw]; ring
  have hwx : |x| * (1 / w) ≤ ε0 := by
    rw [mul_one_div, div_le_iff₀ hw]; exact hx
  have hδ : |δ| ≤ t1 / 4 := by
    rw [habs]
    have : l * |x| * (1 / w) ≤ 2 * ε0 := by
      rw [mul_assoc]
      nlinarith [abs_nonneg x, show 0 ≤ |x| * (1 / w) by positivity]
    linarith
  have t1' : 1 / √N ≤ 2 * (1 / w) := by
    have hsN : 0 < √N := Real.sqrt_pos.2 hN
    have hw' : w = √2 * √N := by rw [hwdef, Real.sqrt_mul (by norm_num)]
    have h2 : √2 ≤ 2 := by
      have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    rw [div_le_iff₀ hsN, hw']
    field_simp
    linarith
  have t2 : |δ| ≤ 2 * |x| * (1 / w) := by
    rw [habs]
    have : 0 ≤ |x| * (1 / w) := by positivity
    nlinarith
  have t3 : N * |δ| ^ 3 ≤ 4 * |x| ^ 3 * (1 / w) := by
    have e : N * |δ| ^ 3 = (1 / 2) * l ^ 3 * |x| ^ 3 * (1 / w) := by
      rw [habs, hNw]; field_simp
    rw [e]
    have hl3 : l ^ 3 ≤ 8 := by
      calc l ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hl.le hl2' 3
        _ = 8 := by norm_num
    have : 0 ≤ |x| ^ 3 * (1 / w) := by positivity
    nlinarith
  have t4 : |x| ≤ 1 + |x| ^ 3 := by
    rcases le_total |x| 1 with h | h
    · linarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3]
    · have h2 : 1 ≤ |x| ^ 2 := by nlinarith
      have : |x| ≤ |x| ^ 3 := by
        calc |x| = |x| * 1 := (mul_one _).symm
          _ ≤ |x| * |x| ^ 2 := by gcongr
          _ = |x| ^ 3 := by ring
      linarith [pow_nonneg (abs_nonneg x) 3]
  have hexp : K * (1 / √N + |δ| + N * |δ| ^ 3) ≤ 6 * K * (1 / w) * (1 + |x| ^ 3) := by
    have hw1 : 0 ≤ 1 / w := by positivity
    have hsum : 1 / √N + |δ| + N * |δ| ^ 3 ≤ (1 / w) * (2 + 2 * |x| + 4 * |x| ^ 3) := by
      linarith
    have hsum2 : (1 / w) * (2 + 2 * |x| + 4 * |x| ^ 3) ≤ 6 * (1 / w) * (1 + |x| ^ 3) := by
      nlinarith
    linarith [mul_le_mul_of_nonneg_left (hsum.trans hsum2) hK]
  obtain ⟨hu, hl'⟩ := H δ hδ
  rw [e1, e2, e3] at hu hl'
  constructor
  · refine le_trans hu ?_
    gcongr
  · refine le_trans ?_ hl'
    gcongr

lemma ZN_low {K t1 ε0 : ℝ} (hK : 0 ≤ K) (ι : Type) [Fintype ι] {σ c tc : ℝ} (hσ : σ ≠ 0)
    (hN0 : 0 < Fintype.card ι) (hL1 : 1 / 2 ≤ L2s G σ tc) (hL3 : L2s G σ tc ≤ 3)
    (hε0 : ε0 ≤ t1 / 8)
    (H : ∀ δ : ℝ, |δ| ≤ t1 / 4 →
      fS G ι σ (Fintype.card ι * (c + δ)) * fS G ι σ (Fintype.card ι * (c - δ))
          ≤ fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(Fintype.card ι * δ ^ 2 / L2s G σ tc)) *
            exp (K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)) ∧
        fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-(Fintype.card ι * δ ^ 2 / L2s G σ tc)) *
            exp (-(K * (1 / √(Fintype.card ι : ℝ) + |δ| + Fintype.card ι * |δ| ^ 3)))
          ≤ fS G ι σ (Fintype.card ι * (c + δ)) * fS G ι σ (Fintype.card ι * (c - δ)))
    (hw1 : 1 ≤ ε0 * √(2 * (Fintype.card ι : ℝ)))
    (hKw : 6 * K * (1 / √(2 * (Fintype.card ι : ℝ))) ≤ 1 / 4) :
    2 * (fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-1)) ≤ ZN G ι σ c tc := by
  have hN : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hN0
  have hs : sN G ι σ tc ≠ 0 := by
    rw [sN]; exact (Real.sqrt_pos.2 (by positivity)).ne'
  have hint := ffN_int (G := G) ι hσ hN0 c tc hs
  set F := fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-1) with hF
  have hF0 : 0 ≤ F := by positivity
  calc 2 * F = ∫ _x in Icc (-1 : ℝ) 1, F := by
        rw [setIntegral_const, measureReal_def, Real.volume_Icc]; norm_num
    _ ≤ ∫ x in Icc (-1 : ℝ) 1, ffN G ι σ c tc x := by
        refine setIntegral_mono_on continuous_const.integrableOn_Icc hint.integrableOn
          measurableSet_Icc fun x hx => ?_
        have hx1 : |x| ≤ 1 := abs_le.2 ⟨hx.1, hx.2⟩
        have hb := (near_x hK ι hN hL1 hL3 hε0 H x (le_trans hx1 hw1)).2
        refine le_trans ?_ hb
        rw [hF, mul_assoc]
        gcongr
        rw [← exp_add]
        gcongr
        have : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
        have h3 : |x| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
        have h4 := mul_le_mul hKw (by linarith : 1 + |x| ^ 3 ≤ 2) (by positivity) (by norm_num)
        linarith
    _ ≤ ZN G ι σ c tc :=
        setIntegral_le_integral hint (Eventually.of_forall fun x => ffN_nonneg ι σ c tc x)

end Nd5

end P99bcb804

end X23_Nd5

section X24_Kl2

/-! R4 / Kl2 (Q6 kernel law, part 2): density disintegration. For `S1, S2` iid `sL G ι σ`, the law
`ρC` of `(S1+S2, S1-S2)` equals `sL G (ι ⊕ ι) σ ⊗ₘ κC`, where `κC T` has density
`gE T d / ZE T`, `gE T d = f((T+d)/2) f((T-d)/2)` (`f = fS`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def fE (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : ℝ → ℝ≥0∞ :=
  fun a => ENNReal.ofReal (fS G ι σ a)

noncomputable def gE (G : Measure ℝ) (ι : Type) [Fintype ι] (σ T d : ℝ) : ℝ≥0∞ :=
  fE G ι σ ((T + d) / 2) * fE G ι σ ((T - d) / 2)

noncomputable def ZE (G : Measure ℝ) (ι : Type) [Fintype ι] (σ T : ℝ) : ℝ≥0∞ :=
  ∫⁻ d, gE G ι σ T d

noncomputable def κC (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : Kernel ℝ ℝ :=
  Kernel.withDensity (Kernel.const ℝ volume) (fun T d => gE G ι σ T d * (ZE G ι σ T)⁻¹)

section Kl2

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma fE_meas (ι : Type) [Fintype ι] (σ : ℝ) : Measurable (fE G ι σ) :=
  ENNReal.measurable_ofReal.comp (fS_meas ι σ)

lemma gE_meas (ι : Type) [Fintype ι] (σ : ℝ) :
    Measurable (fun p : ℝ × ℝ => gE G ι σ p.1 p.2) := by
  have h := fE_meas (G := G) ι σ
  unfold gE
  exact (h.comp (by fun_prop)).mul (h.comp (by fun_prop))

lemma gE_meas_T (ι : Type) [Fintype ι] (σ T : ℝ) : Measurable (fun d => gE G ι σ T d) := by
  have h := fE_meas (G := G) ι σ
  unfold gE
  exact (h.comp (by fun_prop)).mul (h.comp (by fun_prop))

lemma ZE_meas (ι : Type) [Fintype ι] (σ : ℝ) : Measurable (ZE G ι σ) :=
  (gE_meas ι σ).lintegral_prod_right'

lemma dens_meas (ι : Type) [Fintype ι] (σ : ℝ) :
    Measurable (Function.uncurry fun T d => gE G ι σ T d * (ZE G ι σ T)⁻¹) :=
  (gE_meas ι σ).mul ((ZE_meas ι σ).comp measurable_fst).inv

lemma fS_pos (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) (a : ℝ) :
    0 < fS G ι σ a := by
  haveI := sumLaw_prob G ι
  have hv : (Fintype.card ι * σ ^ 2).toNNReal ≠ 0 := by
    have : 0 < (Fintype.card ι : ℝ) * σ ^ 2 := by
      have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
      positivity
    exact (Real.toNNReal_pos.2 this).ne'
  unfold fS
  rw [integral_pos_iff_support_of_nonneg (fun y => gaussianPDFReal_nonneg _ _ _)
    (integrable_pdf_shift _ _ a)]
  have hs : Function.support (fun y => gaussianPDFReal 0 (Fintype.card ι * σ ^ 2).toNNReal (a - y))
      = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (gaussianPDFReal_pos _ _ _ hv).ne'
  rw [hs, measure_univ]
  exact one_pos

lemma ZE_pos (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) (T : ℝ) :
    0 < ZE G ι σ T := by
  unfold ZE
  rw [lintegral_pos_iff_support (gE_meas_T ι σ T)]
  have hs : Function.support (fun d => gE G ι σ T d) = univ := by
    ext d
    simp only [Function.mem_support, mem_univ, iff_true, gE, fE]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (fS_pos ι hσ hN _)).ne'
      (ENNReal.ofReal_pos.2 (fS_pos ι hσ hN _)).ne'
  rw [hs, Real.volume_univ]
  exact ENNReal.zero_lt_top

lemma κC_apply (ι : Type) [Fintype ι] (σ T : ℝ) :
    κC G ι σ T = volume.withDensity (fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹) := by
  rw [κC, Kernel.withDensity_apply _ (dens_meas ι σ), Kernel.const_apply]

end Kl2

end P99bcb804

end X24_Kl2

section X25_Nd6

/-! R4 / Nd6: `node_dthyp`: the standardised conditional density `hN` of the half-difference
given the total satisfies `DtHyp` at `ε = 1/√(2N)` (Q5 node hypotheses). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd6

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma phi_eq (x : ℝ) : phi x = phi 0 * exp (-(x ^ 2 / 2)) := by simp [phi]

lemma far_int (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (ι : Type) [Fintype ι] {σ c tc u r : ℝ} (hσ1 : σ ≤ 1) (hσ0 : 0 < σ) (htc : |tc| ≤ t1 / 2)
    (hu0 : 0 < u) (hu : u ≤ t1 / 2) (hLc : L1s G σ tc = c) (hr : 0 ≤ r)
    (hN0 : 0 < Fintype.card ι) (hs : 0 < sN G ι σ tc) :
    ∫ x in (Icc (-r) r)ᶜ, ffN G ι σ c tc x
      ≤ exp (-(2 * (Fintype.card ι * (tc * c - Ls G σ tc)))) *
          exp (Fintype.card ι * ((3 + B * t1) * u ^ 2)) *
          (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹ ^ 2 *
          (2 * exp (-(u * sN G ι σ tc * r)) / (u * sN G ι σ tc)) := by
  set s := sN G ι σ tc with hsdef
  set C0 := exp (-(2 * (Fintype.card ι * (tc * c - Ls G σ tc)))) *
      exp (Fintype.card ι * ((3 + B * t1) * u ^ 2)) *
      (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹ ^ 2 with hC0
  have hC00 : 0 ≤ C0 := by positivity
  obtain ⟨hgi, hgv⟩ := far_exp (mul_pos hu0 hs) hr
  have hgi' : IntegrableOn (fun x : ℝ => C0 * exp (-(u * s * |x|))) (Iic (-r) ∪ Ioi r) :=
    hgi.const_mul C0
  have hsub : (Icc (-r) r)ᶜ ⊆ Iic (-r) ∪ Ioi r := by
    intro x hx
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact Or.inl (mem_Iic.2 h.le)
    · exact Or.inr (mem_Ioi.2 h)
  have hint := ffN_int (G := G) ι hσ0.ne' hN0 c tc hs.ne'
  calc ∫ x in (Icc (-r) r)ᶜ, ffN G ι σ c tc x
      ≤ ∫ x in (Icc (-r) r)ᶜ, C0 * exp (-(u * s * |x|)) := by
        refine setIntegral_mono_on hint.integrableOn (hgi'.mono_set hsub)
          measurableSet_Icc.compl fun x _ => ?_
        have h := far_pt hexp ht1 h2 hB hV hW ι hσ1 hσ0 htc hu0.le hu hLc (s * x)
        unfold ffN
        refine le_trans h (le_of_eq ?_)
        rw [hC0, abs_mul, abs_of_pos hs, show (Fintype.card ι : ℝ) * ((3 + B * t1) * u ^ 2)
          - u * (s * |x|) = (Fintype.card ι : ℝ) * ((3 + B * t1) * u ^ 2) + -(u * s * |x|) by ring,
          exp_add]
        ring
    _ ≤ ∫ x in Iic (-r) ∪ Ioi r, C0 * exp (-(u * s * |x|)) :=
        setIntegral_mono_set hgi'
          (Eventually.of_forall fun x => by positivity) (Eventually.of_forall hsub)
    _ = C0 * (2 * exp (-(u * s * r)) / (u * s)) := by
        rw [integral_const_mul, hgv]

end Nd6

end P99bcb804

end X25_Nd6

section X26_Nd7

/-! R4 / Nd7: `node_dthyp`: the standardised conditional density `hN` of the half-difference
given the total satisfies `DtHyp` at `ε = 1/√(2N)` (Q5 node hypotheses). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd7

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- the final scalar inequality of the far bound. -/
lemma far_scalar {E X Y W A u s σ L N : ℝ} (hE : 0 < E) (hN : 0 < N) (hL : 0 < L) (hL3 : L ≤ 3)
    (hu : 0 < u) (hs : 1 ≤ s) (hσ : 0 < σ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hW : 0 < W)
    (hXY : X * Y ≤ W * W) (hσW : W ≤ σ ^ 2) (hAu : A * u = 3 * exp 3) :
    E * X * (2 * π * (N * σ ^ 2))⁻¹ * (2 * Y / (u * s)) ≤ A * W * (E * exp (-3) / (π * N * L)) := by
  have hs0 : 0 < s := by linarith
  have hpi := pi_pos
  rw [show E * X * (2 * π * (N * σ ^ 2))⁻¹ * (2 * Y / (u * s))
      = (E * (X * Y)) / (π * N * σ ^ 2 * u * s) by field_simp,
    show A * W * (E * exp (-3) / (π * N * L)) = (A * W * E * exp (-3)) / (π * N * L) by ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have k1 : X * Y * L ≤ 3 * (W * W) := by
    calc X * Y * L ≤ X * Y * 3 := by gcongr
      _ ≤ 3 * (W * W) := by linarith
  have k2 : W * W ≤ W * σ ^ 2 * s := by
    calc W * W ≤ W * σ ^ 2 := by gcongr
      _ = W * σ ^ 2 * 1 := (mul_one _).symm
      _ ≤ W * σ ^ 2 * s := by gcongr
  have k3 : A * W * exp (-3) * (σ ^ 2 * u * s) = 3 * (W * σ ^ 2 * s) := by
    rw [show A * W * exp (-3) * (σ ^ 2 * u * s) = (A * u) * exp (-3) * (W * σ ^ 2 * s) by ring,
      hAu, mul_assoc 3, ← exp_add]
    norm_num
  calc E * (X * Y) * (π * N * L) = (E * π * N) * (X * Y * L) := by ring
    _ ≤ (E * π * N) * (3 * (W * σ ^ 2 * s)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (E * π * N) * (A * W * exp (-3) * (σ ^ 2 * u * s)) := by rw [k3]
    _ = A * W * E * exp (-3) * (π * N * σ ^ 2 * u * s) := by ring

lemma hw1_l {ε0 w N : ℝ} (hε0 : 0 < ε0) (hw : 0 < w) (hw2 : w ^ 2 = 2 * N)
    (hNe : 1 / ε0 ^ 2 ≤ N) : 1 ≤ ε0 * w := by
  have h1 : 1 ≤ ε0 ^ 2 * N := by
    rw [div_le_iff₀ (by positivity)] at hNe; linarith
  have h2 : 1 ≤ (ε0 * w) ^ 2 := by rw [mul_pow, hw2]; linarith
  nlinarith [mul_pos hε0 hw]

lemma hKw_l {K w N : ℝ} (hK : 0 ≤ K) (hw : 0 < w) (hw2 : w ^ 2 = 2 * N)
    (hNK : 288 * K ^ 2 ≤ N) : 6 * K * (1 / w) ≤ 1 / 4 := by
  rw [mul_one_div, div_le_iff₀ hw]
  have h : (24 * K) ^ 2 ≤ w ^ 2 := by rw [hw2]; linarith
  by_contra hc
  push Not at hc
  nlinarith

lemma sr_l {w l N ε0 : ℝ} (hw2 : w ^ 2 = 2 * N) (hN : 0 < N) (hl : 1 / 2 ≤ l) (hε0 : 0 < ε0) :
    N * ε0 ≤ w * l * (ε0 * w) := by
  have : w * l * (ε0 * w) = w ^ 2 * ε0 * l := by ring
  rw [this, hw2]; nlinarith [mul_pos hN hε0]

lemma s1_l {w l N : ℝ} (hw : 0 < w) (hw2 : w ^ 2 = 2 * N) (hN : 2 ≤ N) (hl : 1 / 2 ≤ l) :
    1 ≤ w * l := by
  have : 2 ≤ w := by nlinarith
  nlinarith

lemma xy_l {N Lb ε0 S u b : ℝ} (hLb : 0 < Lb) (hε0 : 0 < ε0) (hu : u = ε0 / (2 * Lb))
    (hb : b = ε0 ^ 2 / (16 * Lb)) (hS : N * ε0 ≤ S) :
    exp (N * (Lb * u ^ 2)) * exp (-(u * S)) ≤ exp (-(2 * N * b)) * exp (-(2 * N * b)) := by
  subst hu hb
  rw [← exp_add, ← exp_add]
  apply exp_le_exp.2
  have h1 : ε0 / (2 * Lb) * (N * ε0) ≤ ε0 / (2 * Lb) * S :=
    mul_le_mul_of_nonneg_left hS (by positivity)
  have h2 : N * (Lb * (ε0 / (2 * Lb)) ^ 2) - ε0 / (2 * Lb) * (N * ε0)
      = -(2 * N * (ε0 ^ 2 / (16 * Lb))) + -(2 * N * (ε0 ^ 2 / (16 * Lb))) := by
    field_simp; ring
  linarith

lemma sig_l {σ N b : ℝ} (hσ : 0 < σ) (h : σ⁻¹ ≤ exp (b * N)) : exp (-(2 * N * b)) ≤ σ ^ 2 := by
  have h1 : exp (-(N * b)) ≤ σ := by
    rw [exp_neg, inv_le_comm₀ (exp_pos _) hσ, mul_comm]; exact h
  calc exp (-(2 * N * b)) = exp (-(N * b)) ^ 2 := by
        rw [sq, ← exp_add]; congr 1; ring
    _ ≤ σ ^ 2 := pow_le_pow_left₀ (exp_pos _).le h1 2

lemma Au_l {ε0 Lb A u : ℝ} (hε0 : 0 < ε0) (hLb : 0 < Lb) (hA : A = 6 * exp 3 * Lb / ε0)
    (hu : u = ε0 / (2 * Lb)) : A * u = 3 * exp 3 := by
  subst hA hu; field_simp; ring

lemma zl_l {E e1 F Z N L : ℝ} (hN : 0 < N) (hL : 0 < L) (hE1 : e1 ^ 2 = E)
    (hFlow : e1 * ((√(2 * π * N))⁻¹ * (√L)⁻¹) * exp (-1) ≤ F) (he1 : 0 < e1)
    (hZ : 2 * (F ^ 2 * exp (-1)) ≤ Z) : E * exp (-3) / (π * N * L) ≤ Z := by
  have hQ : ((√(2 * π * N))⁻¹ * (√L)⁻¹) ^ 2 = (2 * π * N * L)⁻¹ := by
    rw [mul_pow, inv_pow, inv_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hL.le, ← mul_inv]
  have hF2 : (e1 * ((√(2 * π * N))⁻¹ * (√L)⁻¹) * exp (-1)) ^ 2 ≤ F ^ 2 :=
    pow_le_pow_left₀ (by positivity) hFlow 2
  rw [mul_pow, mul_pow, hE1, hQ] at hF2
  have he : exp (-1) ^ 2 * exp (-1) = exp (-3) := by
    rw [sq, ← exp_add, ← exp_add]; norm_num
  calc E * exp (-3) / (π * N * L) = 2 * (E * (2 * π * N * L)⁻¹ * exp (-1) ^ 2 * exp (-1)) := by
        rw [mul_assoc (E * (2 * π * N * L)⁻¹), he]; ring
    _ ≤ 2 * (F ^ 2 * exp (-1)) := by gcongr
    _ ≤ Z := hZ

lemma kphi_eq {F Z p e1 e2 : ℝ} (hZ : Z ≠ 0) (hp : p ≠ 0) :
    F ^ 2 / (Z * p) * (p * e1) * e2 * Z = F ^ 2 * e1 * e2 := by
  field_simp

set_option maxHeartbeats 1000000 in
lemma far_conj (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (ι : Type) [Fintype ι] {σ c tc Lb ε0 u b A w : ℝ} (hσ1 : σ ≤ 1) (hσ : 0 < σ)
    (htc : |tc| ≤ t1 / 2) (hLc : L1s G σ tc = c)
    (hLb : Lb = 3 + B * t1) (hu : u = ε0 / (2 * Lb)) (hb : b = ε0 ^ 2 / (16 * Lb))
    (hA : A = 6 * exp 3 * Lb / ε0) (hε0 : 0 < ε0) (hε0t : ε0 ≤ t1 / 8)
    (hw : 0 < w) (hw2 : w ^ 2 = 2 * (Fintype.card ι : ℝ)) (hN2 : (2 : ℝ) ≤ Fintype.card ι)
    (hN0 : 0 < Fintype.card ι)
    (hZ : 2 * (fS G ι σ (Fintype.card ι * c) ^ 2 * exp (-1)) ≤ ZN G ι σ c tc)
    (hFlow : exp (-(Fintype.card ι * (tc * c - Ls G σ tc))) *
            ((√(2 * π * Fintype.card ι))⁻¹ * (√(L2s G σ tc))⁻¹) * exp (-1)
          ≤ fS G ι σ (Fintype.card ι * c))
    (hL1 : 1 / 2 ≤ L2s G σ tc) (hL3 : L2s G σ tc ≤ 3)
    (hσb : σ⁻¹ ≤ exp (b * Fintype.card ι)) (hs : sN G ι σ tc = w * √(L2s G σ tc)) :
    ∫ x in (Icc (-(ε0 * w)) (ε0 * w))ᶜ, ffN G ι σ c tc x
      ≤ A * exp (-(2 * (Fintype.card ι : ℝ) * b)) * ZN G ι σ c tc := by
  have hLb3 : 3 ≤ Lb := by rw [hLb]; have := mul_nonneg hB ht1.le; linarith
  have hLb0 : 0 < Lb := by linarith
  have hN : (0 : ℝ) < Fintype.card ι := by linarith
  have hu0 : 0 < u := by rw [hu]; positivity
  have hut : u ≤ t1 / 2 := by
    rw [hu, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hLb3 ht1.le
    linarith
  have hl : 1 / 2 ≤ √(L2s G σ tc) := (Real.le_sqrt' (by norm_num)).2 (by linarith)
  have hs0 : 0 < sN G ι σ tc := by rw [hs]; have := hw; positivity
  have hfar := far_int hexp ht1 h2 hB hV hW ι hσ1 hσ htc hu0 hut hLc
    (by positivity : 0 ≤ ε0 * w) hN0 hs0
  refine le_trans hfar ?_
  rw [← hLb, inv_pow, Real.sq_sqrt (by positivity)]
  have hE1 : exp (-((Fintype.card ι : ℝ) * (tc * c - Ls G σ tc))) ^ 2
      = exp (-(2 * ((Fintype.card ι : ℝ) * (tc * c - Ls G σ tc)))) := by
    rw [sq, ← exp_add]; congr 1; ring
  have hZl := zl_l hN (by linarith) hE1 hFlow (exp_pos _) hZ
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hZl (by rw [hA]; positivity))
  refine far_scalar (exp_pos _) hN (by linarith) hL3 hu0 ?_ hσ (exp_pos _).le (exp_pos _).le
    (exp_pos _) ?_ (sig_l hσ (by rw [hb] at hσb ⊢; exact hσb)) (Au_l hε0 hLb0 hA hu)
  · rw [hs]; exact s1_l hw hw2 hN2 hl
  · have hS : (Fintype.card ι : ℝ) * ε0 ≤ sN G ι σ tc * (ε0 * w) := by
      rw [hs]; exact sr_l hw2 hN hl hε0
    have h := xy_l hLb0 hε0 hu hb hS
    rwa [← mul_assoc u] at h

set_option maxHeartbeats 1000000 in
theorem node_dthyp (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ c0 ε0 A b β N2 : ℝ, 0 ≤ c0 ∧ 0 < ε0 ∧ c0 * ε0 ≤ 1 / 16 ∧ 0 ≤ A ∧ 0 < b ∧ 0 < β ∧
      ∀ (ι : Type) [Fintype ι] (σ c tc : ℝ), 0 < σ → σ ≤ 1 → N2 ≤ (Fintype.card ι : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card ι) → |c| ≤ t1 / 4 → |tc| ≤ t1 / 2 → L1s G σ tc = c →
        DtHyp c0 ε0 A b (hN G ι σ c tc)
          (fS G ι σ (Fintype.card ι * c) ^ 2 / (ZN G ι σ c tc * phi 0))
          (1 / √(2 * (Fintype.card ι : ℝ))) := by
  obtain ⟨κ', K, N1, hκ0, hκ1, hK, H⟩ :=
    near_ratio ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  set Lb := 3 + B * t1 with hLb
  have hLb3 : 3 ≤ Lb := by have := mul_nonneg hB ht1.le; linarith
  set c0 := 6 * K with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set ε0 := min (t1 / 8) (1 / (16 * (c0 + 1))) with hε0
  have hε0p : 0 < ε0 := lt_min (by positivity) (by positivity)
  have hε0t : ε0 ≤ t1 / 8 := min_le_left _ _
  have hc0ε0 : c0 * ε0 ≤ 1 / 16 := by
    have h1 : ε0 ≤ 1 / (16 * (c0 + 1)) := min_le_right _ _
    calc c0 * ε0 ≤ c0 * (1 / (16 * (c0 + 1))) := by gcongr
      _ ≤ 1 / 16 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
  set u := ε0 / (2 * Lb) with hu
  set b := ε0 ^ 2 / (16 * Lb) with hb
  set A := 6 * exp 3 * Lb / ε0 with hA
  set β := min b (κ' / 2) with hβ
  have hb0 : 0 < b := by positivity
  set N2 := max (max N1 (8 * exp κ' / κ' ^ 2)) (max 2 (max (1 / ε0 ^ 2) (288 * K ^ 2))) with hN2
  refine ⟨c0, ε0, A, b, β, N2, hc00, hε0p, hc0ε0, by positivity, hb0, lt_min hb0 (by positivity), ?_⟩
  intro ι _ σ c tc hσ hσ1 hNN hσβ hc htc hLc
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN2' : (2 : ℝ) ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hNN
  have hNnat : 2 ≤ Fintype.card ι := by
    have h : ((2 : ℕ) : ℝ) ≤ ((Fintype.card ι : ℕ) : ℝ) := by rw [← hNdef]; simpa using hN2'
    exact_mod_cast h
  have hN0 : 0 < Fintype.card ι := by omega
  have hN : 0 < N := by linarith
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNN
  have hNk : 8 * exp κ' / κ' ^ 2 ≤ N :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNN
  have hNe : 1 / ε0 ^ 2 ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hNN
  have hNK : 288 * K ^ 2 ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hNN
  have hσb : σ⁻¹ ≤ exp (b * N) :=
    hσβ.trans (exp_le_exp.2 (mul_le_mul_of_nonneg_right (min_le_left _ _) hN.le))
  have hκc : (1 - κ') ^ (Fintype.card ι - 1) / σ ≤ 1 / N :=
    kappa_cond hκ0 hκ1 _ hNk hNnat σ hσ (hσβ.trans (exp_le_exp.2
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hN.le)))
  have htc1 : |tc| ≤ t1 := by linarith
  have Hδ := fun δ (hδ : |δ| ≤ t1 / 4) =>
    (H ι σ c δ tc hσ hσ1 hNN1 hNnat hκc hc hδ htc1 hLc).2.2
  have H0 := H ι σ c 0 tc hσ hσ1 hNN1 hNnat hκc hc (by simp; positivity) htc1 hLc
  have hF0 : 0 < fS G ι σ (N * c) := H0.1
  have hFlow := H0.2.1
  have hL1 : 1 / 2 ≤ L2s G σ tc := by
    have := (hV tc htc1).1; simp only [L2s]; linarith [sq_nonneg σ]
  have hL3 : L2s G σ tc ≤ 3 := by
    have := (hV tc htc1).2
    have : σ ^ 2 ≤ 1 := pow_le_one₀ hσ.le hσ1
    simp only [L2s]; linarith
  have hw : 0 < √(2 * N) := Real.sqrt_pos.2 (by positivity)
  have hw2 : √(2 * N) ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hw1 := hw1_l hε0p hw hw2 hNe
  have hKw := hKw_l hK hw hw2 hNK
  have hZ := ZN_low hK ι hσ.ne' hN0 hL1 hL3 hε0t Hδ hw1 hKw
  have hZ0 : 0 < ZN G ι σ c tc := lt_of_lt_of_le (by positivity) hZ
  have hphi := phi_pos 0
  have hs : sN G ι σ tc = √(2 * N) * √(L2s G σ tc) := by
    rw [sN, ← hNdef, Real.sqrt_mul (by positivity)]
  have hs0 : 0 < sN G ι σ tc := by
    rw [hs]; have : 0 < √(L2s G σ tc) := Real.sqrt_pos.2 (by linarith); positivity
  have hrw : ε0 / (1 / √(2 * N)) = ε0 * √(2 * N) := by rw [one_div, div_inv_eq_mul]
  have hbe : b / (1 / √(2 * N)) ^ 2 = 2 * N * b := by rw [div_pow, hw2]; field_simp
  refine ⟨by positivity, by positivity, fun x => div_nonneg (ffN_nonneg ι σ c tc x) hZ0.le,
    (ffN_int ι hσ.ne' hN0 c tc hs0.ne').div_const _, ?_, ?_, ?_, ?_⟩
  · show ∫ x, ffN G ι σ c tc x / ZN G ι σ c tc = 1
    rw [integral_div]; exact div_self hZ0.ne'
  · intro x hx
    rw [hrw] at hx
    have hb := (near_x hK ι hN hL1 hL3 hε0t Hδ x hx).1
    show ffN G ι σ c tc x / ZN G ι σ c tc ≤ fS G ι σ (N * c) ^ 2 / (ZN G ι σ c tc * phi 0) *
      phi x * exp (6 * K * (1 / √(2 * N)) * (1 + |x| ^ 3))
    rw [phi_eq x, div_le_iff₀ hZ0, kphi_eq hZ0.ne' hphi.ne']
    exact hb
  · intro x hx
    rw [hrw] at hx
    have hb := (near_x hK ι hN hL1 hL3 hε0t Hδ x hx).2
    show fS G ι σ (N * c) ^ 2 / (ZN G ι σ c tc * phi 0) * phi x *
      exp (-(6 * K * (1 / √(2 * N)) * (1 + |x| ^ 3))) ≤ ffN G ι σ c tc x / ZN G ι σ c tc
    rw [phi_eq x, le_div_iff₀ hZ0, kphi_eq hZ0.ne' hphi.ne']
    exact hb
  · rw [hrw, hbe]
    show ∫ x in (Icc (-(ε0 * √(2 * N))) (ε0 * √(2 * N)))ᶜ, ffN G ι σ c tc x / ZN G ι σ c tc
      ≤ A * exp (-(2 * N * b))
    rw [integral_div, div_le_iff₀ hZ0]
    exact far_conj hexp ht1 h2 hB hV hW ι hσ1 hσ htc hLc rfl rfl rfl rfl hε0p hε0t hw hw2 hN2'
      hN0 hZ hFlow hL1 hL3 hσb hs

end Nd7

end P99bcb804

end X26_Nd7

section X30_DtG

/-! R4 / DtG: bridge from the density hypotheses `DtHyp` (at `ε = 1/√m`) to the Tusnady sandwich
for the law `L = (volume.withDensity h).map (√m * ·)` via `tusnady_one`. -/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace P99bcb804

lemma dens_prob {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hint : Integrable h) (h1 : ∫ x, h x = 1) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (h x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => hh0 x), h1,
    ENNReal.ofReal_one]

lemma map_real {μ : Measure ℝ} {σ : ℝ} (S : Set ℝ) (hS : MeasurableSet S) :
    (μ.map (fun x => σ * x)).real S = μ.real ((fun x => σ * x) ⁻¹' S) := by
  rw [measureReal_def, measureReal_def, Measure.map_apply (measurable_const_mul σ) hS]

lemma pre_Iic {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : (fun x => σ * x) ⁻¹' Iic y = Iic (y / σ) := by
  ext x; simp only [mem_preimage, mem_Iic]; rw [le_div_iff₀ hσ, mul_comm]

end P99bcb804

end X30_DtG

section X44_Qt

/-! Quantile toolkit (from _qt.lean) and Tusnady arithmetic (from _tq.lean), plus a uniform
single-measure Tusnady sandwich `tusnady_one` for the dyadic node (4.12). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

lemma Phi_strictMono : StrictMono Phi :=
  strictMono_of_deriv_pos (fun x => by rw [(hasDerivAt_Phi x).deriv]; exact phi_pos x)

/-- Generalized inverse (quantile function) of a law on `ℝ`. -/
noncomputable def qnt (L : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf L x}

lemma qnt_le_iff (L : Measure ℝ) [IsProbabilityMeasure L] {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (x : ℝ) : qnt L u ≤ x ↔ u ≤ cdf L x := by
  set A := {x | u ≤ cdf L x} with hA
  have hne : A.Nonempty := ((tendsto_cdf_atTop L).eventually (lt_mem_nhds hu1)).exists.imp
    fun x hx => hx.le
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp ((tendsto_cdf_atBot L).eventually (gt_mem_nhds hu0))
  have hbdd : BddBelow A := ⟨b, fun a ha => by
    by_contra h
    have := hb a (not_le.mp h).le
    exact absurd ha (not_le.mpr this)⟩
  constructor
  · intro hq
    have hq0 : u ≤ cdf L (qnt L u) := by
      have hyy : ∀ y ∈ Set.Ioi (qnt L u), u ≤ cdf L y := by
        intro y hy
        obtain ⟨a, ha, hay⟩ := exists_lt_of_csInf_lt hne hy
        exact ha.trans ((cdf L).mono hay.le)
      have ht : Tendsto (cdf L) (𝓝[>] (qnt L u)) (𝓝 (cdf L (qnt L u))) :=
        ((cdf L).right_continuous _).mono Set.Ioi_subset_Ici_self
      exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall hyy)
    exact hq0.trans ((cdf L).mono hq)
  · intro hx
    exact csInf_le hbdd hx

lemma Phi_pos' (w : ℝ) : 0 < Phi w := cdf_std_pos w

lemma Phi_lt_one (w : ℝ) : Phi w < 1 := cdf_std_lt_one w

/-- A Tusnády sandwich turns into a pointwise bound on the quantile transform. -/
lemma qnt_close (L : Measure ℝ) [IsProbabilityMeasure L] {s E : ℝ} (hs : 0 < s)
    (δ : ℝ → ℝ) (hδ : Continuous δ)
    (H : ∀ y : ℝ, |y| ≤ E → Phi (y / s) ≤ cdf L (y + δ y) ∧ cdf L (y - δ y) ≤ Phi (y / s))
    {w : ℝ} (hw : |w| < E) : |qnt L (Phi (w / s)) - w| ≤ δ w := by
  have hu0 := Phi_pos' (w / s)
  have hu1 := Phi_lt_one (w / s)
  rw [abs_le]
  constructor
  · by_contra hlt
    rw [not_le] at hlt
    set x := qnt L (Phi (w / s)) with hx
    have hxw : x < w - δ w := by linarith
    have hux : Phi (w / s) ≤ cdf L x := (qnt_le_iff L hu0 hu1 x).mp le_rfl
    have hopen : IsOpen {y : ℝ | x < y - δ y ∧ |y| < E} :=
      (isOpen_lt continuous_const (continuous_id.sub hδ)).inter
        (isOpen_lt continuous_abs continuous_const)
    have hev : ∀ᶠ y in 𝓝[<] w, x < y - δ y ∧ |y| < E ∧ y < w := by
      have h1 : ∀ᶠ y in 𝓝[<] w, x < y - δ y ∧ |y| < E :=
        nhdsWithin_le_nhds (hopen.mem_nhds ⟨hxw, hw⟩)
      filter_upwards [h1, self_mem_nhdsWithin] with y hy hy' using ⟨hy.1, hy.2, hy'⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := hev.exists
    have hH := (H y hy2.le).2
    have hlt2 : Phi (y / s) < Phi (w / s) := Phi_strictMono (div_lt_div_of_pos_right hy3 hs)
    have hmono : cdf L x ≤ cdf L (y - δ y) := (cdf L).mono hy1.le
    linarith
  · have := (H w hw.le).1
    have := (qnt_le_iff L hu0 hu1 (w + δ w)).mpr this
    linarith

end P99bcb804

end X44_Qt

section X45_DtH

/-! R4 / DtH: `dt_tusnady`: density hypotheses at `ε = 1/√m` give the Tusnady sandwich for
`L = (volume.withDensity h).map (√m * ·)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace P99bcb804

theorem dt_tusnady :
    ∀ {c0 ε0 A b : ℝ},
      (0 : ℝ) ≤ c0 →
        (0 : ℝ) < ε0 →
          c0 * ε0 ≤ (1 / 16 : ℝ) →
            (0 : ℝ) ≤ A →
              (0 : ℝ) < b →
                ∃ (c : ℝ) (εt : ℝ) (m₀ : ℕ),
                  (0 : ℝ) < c ∧
                    (0 : ℝ) < εt ∧
                      (1 : ℕ) ≤ m₀ ∧
                        ∀ (m : ℕ),
                          m₀ ≤ m →
                            ∀ (h : ℝ → ℝ) (K0 : ℝ),
                              P99bcb804.DtHyp c0 ε0 A b h K0 ((1 : ℝ) / √↑m) →
                                ∀ (y : ℝ),
                                  |y| ≤ εt * ↑m →
                                    P99bcb804.Phi (y / √↑m) ≤
                                        (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y + c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ∧
                                      (ProbabilityTheory.cdf
                                              (MeasureTheory.Measure.map (fun (x : ℝ) => √↑m * x)
                                                (MeasureTheory.Measure.withDensity MeasureTheory.MeasureSpace.volume
                                                  fun (x : ℝ) => ENNReal.ofReal (h x))))
                                          (y - c * ((1 : ℝ) + y ^ (2 : ℕ) / ↑m)) ≤
                                        P99bcb804.Phi (y / √↑m) := EthierKurtz.gaussian_density_perturbation_quantile_sandwich

end P99bcb804

end X45_DtH

section X46_Nd8

/-! R4 / Nd8: Q5 node quantile bound. `KN` = law of the half-difference `d = sN x` given the total
(`x ~ hN`). `node_qtc`: `|qnt KN (Φ(w/√m)) - √(L2s tc) w| ≤ C(1 + w²/m)`, `m = 2N`.
`node_q0`: with the fixed scale `l0 = √(L2s 0)`: `|qnt KN (Φ(u/(l0√m))) - u| ≤ C(1 + u²/m + c² m)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def KN (G : Measure ℝ) (ι : Type) [Fintype ι] (σ c tc : ℝ) : Measure ℝ :=
  (volume.withDensity (fun x => ENNReal.ofReal (hN G ι σ c tc x))).map
    (fun x => sN G ι σ tc * x)

lemma qnt_map_mul (L : Measure ℝ) [IsProbabilityMeasure L] {k : ℝ} (hk : 0 < k) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    qnt (L.map (fun x => k * x)) u = k * qnt L u := by
  haveI : IsProbabilityMeasure (L.map (fun x => k * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul k).aemeasurable
  have key : ∀ z, qnt (L.map (fun x => k * x)) u ≤ z ↔ k * qnt L u ≤ z := by
    intro z
    have h2 : k * qnt L u ≤ z ↔ qnt L u ≤ z / k := by
      rw [le_div_iff₀ hk, mul_comm]
    rw [h2, qnt_le_iff _ hu0 hu1, qnt_le_iff L hu0 hu1, cdf_eq_real, cdf_eq_real,
      map_real _ measurableSet_Iic, pre_Iic hk]
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

lemma sqrt_diff {a b : ℝ} (ha : 1 / 2 ≤ a) (hb : 1 / 2 ≤ b) : |√a - √b| ≤ |a - b| := by
  have h1 : √(1 / 4) ≤ √a := Real.sqrt_le_sqrt (by linarith)
  have h2 : √(1 / 4) ≤ √b := Real.sqrt_le_sqrt (by linarith)
  have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h1 h2
  have e : a - b = (√a - √b) * (√a + √b) := by
    rw [show (√a - √b) * (√a + √b) = √a ^ 2 - √b ^ 2 by ring, Real.sq_sqrt (by linarith),
      Real.sq_sqrt (by linarith)]
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < √a + √b)]
  have := abs_nonneg (√a - √b)
  nlinarith

lemma amgm_cu {c u M : ℝ} (hM : 0 < M) : |c| * |u| ≤ (c ^ 2 * M + u ^ 2 / M) / 2 := by
  have e : (c ^ 2 * M + u ^ 2 / M) / 2 - |c| * |u| = (|c| * M - |u|) ^ 2 / (2 * M) := by
    rw [← sq_abs c, ← sq_abs u]
    field_simp
    ring
  have : 0 ≤ (|c| * M - |u|) ^ 2 / (2 * M) := by positivity
  linarith

lemma fin_q0 {Q l l0 u c M C1 B : ℝ} (hM : 0 < M) (hl0 : 1 / 2 ≤ l0) (hC1 : 0 ≤ C1)
    (hB : 0 ≤ B) (hQ : |Q - l * (u / l0)| ≤ C1 * (1 + (u / l0) ^ 2 / M))
    (hll : |l - l0| ≤ 2 * B * |c|) :
    |Q - u| ≤ (4 * C1 + 4 * B) * (1 + u ^ 2 / M + c ^ 2 * M) := by
  have hl0p : 0 < l0 := by linarith
  set w := u / l0 with hwd
  have hu : u = l0 * w := by rw [hwd]; field_simp
  have hw2 : |w| ≤ 2 * |u| := by
    rw [hwd, abs_div, abs_of_pos hl0p, div_le_iff₀ hl0p]
    have := abs_nonneg u
    nlinarith
  have hww : w ^ 2 ≤ 4 * u ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg w) hw2 2
    rw [sq_abs, mul_pow, sq_abs] at h
    linarith
  have hsplit : Q - u = (Q - l * w) + (l - l0) * w := by rw [hu]; ring
  have hA : |(l - l0) * w| ≤ 4 * B * (|c| * |u|) := by
    rw [abs_mul]
    calc |l - l0| * |w| ≤ (2 * B * |c|) * (2 * |u|) :=
          mul_le_mul hll hw2 (abs_nonneg _) (by positivity)
      _ = 4 * B * (|c| * |u|) := by ring
  have hcu := amgm_cu (c := c) (u := u) hM
  have hwM : w ^ 2 / M ≤ 4 * (u ^ 2 / M) := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right hww hM.le
  have hQ' : |Q - l * w| ≤ C1 * (1 + 4 * (u ^ 2 / M)) :=
    hQ.trans (mul_le_mul_of_nonneg_left (by linarith) hC1)
  have hu2 : 0 ≤ u ^ 2 / M := by positivity
  have hc2 : 0 ≤ c ^ 2 * M := by positivity
  rw [hsplit]
  calc |(Q - l * w) + (l - l0) * w| ≤ |Q - l * w| + |(l - l0) * w| := abs_add_le _ _
    _ ≤ C1 * (1 + 4 * (u ^ 2 / M)) + 4 * B * ((c ^ 2 * M + u ^ 2 / M) / 2) := by
        gcongr
        exact hA.trans (mul_le_mul_of_nonneg_left hcu (by positivity))
    _ ≤ (4 * C1 + 4 * B) * (1 + u ^ 2 / M + c ^ 2 * M) := by
        have h1 : 0 ≤ C1 * (u ^ 2 / M) := mul_nonneg hC1 hu2
        have h2 : 0 ≤ C1 * (c ^ 2 * M) := mul_nonneg hC1 hc2
        have h3 : 0 ≤ B * (u ^ 2 / M) := mul_nonneg hB hu2
        have h4 : 0 ≤ B * (c ^ 2 * M) := mul_nonneg hB hc2
        linarith

section Nd8

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma V_lip (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {t : ℝ} (ht : |t| ≤ t1) :
    |iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t - iteratedDeriv 2 (cgf (fun x : ℝ => x) G) 0|
      ≤ B * |t| := by
  have hd : ∀ x ∈ Icc (-t1) t1,
      DifferentiableAt ℝ (iteratedDeriv 2 (cgf (fun x : ℝ => x) G)) x := by
    intro x hx
    exact (an_cgf hexp 2 x ⟨by linarith [hx.1], by linarith [hx.2]⟩).differentiableAt
  have hb : ∀ x ∈ Icc (-t1) t1,
      ‖deriv (iteratedDeriv 2 (cgf (fun x : ℝ => x) G)) x‖ ≤ B := by
    intro x hx
    rw [← iteratedDeriv_succ, Real.norm_eq_abs]
    exact hW x ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h0 : (0 : ℝ) ∈ Icc (-t1) t1 := ⟨by linarith, by linarith⟩
  have := (convex_Icc (-t1) t1).norm_image_sub_le_of_norm_deriv_le hd hb h0 (abs_le.1 ht)
  simpa [Real.norm_eq_abs] using this

lemma tc_bound (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 : ℝ} (h2 : 2 * t1 < a0) (ht1 : 0 < t1)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) (σ : ℝ) {tc c : ℝ}
    (htc : |tc| ≤ t1) (hL : L1s G σ tc = c) : |tc| ≤ 2 * |c| := by
  have h0 : L1s G σ 0 = 0 := by simp [L1s, tmu_zero ha0 hexp hm]
  have hz : |(0 : ℝ)| ≤ t1 := by simpa using ht1.le
  rcases le_total 0 tc with h | h
  · have := L1s_mono hexp h2 ht1 hV σ hz htc h
    rw [h0, hL] at this
    rw [abs_of_nonneg h]; linarith [le_abs_self c]
  · have := L1s_mono hexp h2 ht1 hV σ htc hz h
    rw [h0, hL] at this
    rw [abs_of_nonpos h]; linarith [neg_abs_le c]

lemma L2s_bd {t1 : ℝ}
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (ht : |t| ≤ t1) : 1 / 2 ≤ L2s G σ t ∧ L2s G σ t ≤ 3 := by
  have h := hV t ht
  have hs : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0.le hσ1
  have hs0 : 0 ≤ σ ^ 2 := sq_nonneg σ
  rw [L2s]
  constructor <;> linarith [h.1, h.2]

theorem node_qtc (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C εq β N3 : ℝ, 0 < C ∧ 0 < εq ∧ 0 < β ∧ 1 ≤ N3 ∧
      ∀ (ι : Type) [Fintype ι] (σ c tc : ℝ), 0 < σ → σ ≤ 1 → N3 ≤ (Fintype.card ι : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card ι) → |c| ≤ t1 / 4 → |tc| ≤ t1 / 2 → L1s G σ tc = c →
        ∀ w : ℝ, |w| < εq * (2 * Fintype.card ι) →
          |qnt (KN G ι σ c tc) (Phi (w / √(2 * (Fintype.card ι : ℝ)))) -
              √(L2s G σ tc) * w| ≤ C * (1 + w ^ 2 / (2 * Fintype.card ι)) := by
  obtain ⟨c0, ε0, A, b, β, N2, hc0, hε0, hce, hA, hb, hβ, HD⟩ :=
    node_dthyp ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  obtain ⟨cq, εt, m₀, hcq, hεt, hm₀, HT⟩ := dt_tusnady hc0 hε0 hce hA hb
  have hm₀r : (1 : ℝ) ≤ m₀ := by exact_mod_cast hm₀
  refine ⟨cq * √3, εt, β, max N2 (m₀ : ℝ), by positivity, hεt, hβ,
    le_trans hm₀r (le_max_right _ _), ?_⟩
  intro ι _ σ c tc hσ0 hσ1 hNn hσβ hc htc hL w hw
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * Fintype.card ι := ⟨_, rfl⟩
  have hMr : (M : ℝ) = 2 * (Fintype.card ι : ℝ) := by rw [hM]; push_cast; ring
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := le_trans hm₀r (le_trans (le_max_right _ _) hNn)
  have hMp : 0 < (M : ℝ) := by rw [hMr]; linarith
  have hm0 : m₀ ≤ M := by
    have : (m₀ : ℝ) ≤ (M : ℝ) := by rw [hMr]; linarith [le_max_right N2 (m₀ : ℝ)]
    exact_mod_cast this
  have hD := HD ι σ c tc hσ0 hσ1 (le_trans (le_max_left _ _) hNn) hσβ hc htc hL
  rw [← hMr] at hD
  have HT' := HT M hm0 _ _ hD
  obtain ⟨-, -, h0, hint, h1, -⟩ := hD
  haveI := dens_prob h0 hint h1
  obtain ⟨L, hLd⟩ : ∃ L : Measure ℝ, L = (volume.withDensity
      (fun x => ENNReal.ofReal (hN G ι σ c tc x))).map (fun x => √(M : ℝ) * x) := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure L := by
    rw [hLd]; exact Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  rw [← hLd] at HT'
  have hsM : 0 < √(M : ℝ) := Real.sqrt_pos.2 hMp
  rw [← hMr] at hw ⊢
  have hq : |qnt L (Phi (w / √(M : ℝ))) - w| ≤ cq * (1 + w ^ 2 / M) :=
    qnt_close L hsM (fun y => cq * (1 + y ^ 2 / M)) (by fun_prop) (E := εt * M)
      (fun y hy => HT' y hy) hw
  have hlb := L2s_bd hV hσ0 hσ1 (le_trans htc (by linarith) : |tc| ≤ t1)
  have hl : 0 < √(L2s G σ tc) := Real.sqrt_pos.2 (by linarith [hlb.1])
  have hl3 : √(L2s G σ tc) ≤ √3 := Real.sqrt_le_sqrt hlb.2
  have hK : KN G ι σ c tc = L.map (fun x => √(L2s G σ tc) * x) := by
    rw [KN, hLd, Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1
    funext x
    simp only [Function.comp, sN]
    rw [Real.sqrt_mul (by positivity), ← hMr]
    ring
  rw [hK, qnt_map_mul L hl (Phi_pos' _) (Phi_lt_one _), ← mul_sub, abs_mul, abs_of_pos hl]
  calc √(L2s G σ tc) * |qnt L (Phi (w / √(M : ℝ))) - w|
      ≤ √3 * (cq * (1 + w ^ 2 / M)) := mul_le_mul hl3 hq (abs_nonneg _) (by positivity)
    _ = cq * √3 * (1 + w ^ 2 / M) := by ring

theorem node_q0 (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C εq β N3 : ℝ, 0 < C ∧ 0 < εq ∧ 0 < β ∧ 1 ≤ N3 ∧
      ∀ (ι : Type) [Fintype ι] (σ c tc : ℝ), 0 < σ → σ ≤ 1 → N3 ≤ (Fintype.card ι : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card ι) → |c| ≤ t1 / 4 → |tc| ≤ t1 / 2 → L1s G σ tc = c →
        ∀ u : ℝ, |u| < εq * (2 * Fintype.card ι) →
          |qnt (KN G ι σ c tc) (Phi (u / (√(L2s G σ 0) * √(2 * (Fintype.card ι : ℝ))))) - u|
            ≤ C * (1 + u ^ 2 / (2 * Fintype.card ι) + c ^ 2 * (2 * Fintype.card ι)) := by
  obtain ⟨C1, εq, β, N3, hC1, hεq, hβ, hN3, H⟩ :=
    node_qtc ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  refine ⟨4 * C1 + 4 * B, εq / 2, β, N3, by positivity, by positivity, hβ, hN3, ?_⟩
  intro ι _ σ c tc hσ0 hσ1 hNn hσβ hc htc hL u hu
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := le_trans hN3 hNn
  have hMp : 0 < 2 * (Fintype.card ι : ℝ) := by linarith
  have hz : |(0 : ℝ)| ≤ t1 := by simpa using ht1.le
  have hl0b := L2s_bd hV hσ0 hσ1 hz
  have htc1 : |tc| ≤ t1 := le_trans htc (by linarith)
  have hlb := L2s_bd hV hσ0 hσ1 htc1
  have hl0 : 1 / 2 ≤ √(L2s G σ 0) := by
    have h1 : √(1 / 4) ≤ √(L2s G σ 0) := Real.sqrt_le_sqrt (by linarith [hl0b.1])
    have h4 : √(1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at h1
  have hl0p : 0 < √(L2s G σ 0) := by linarith
  have hw : |u / √(L2s G σ 0)| < εq * (2 * Fintype.card ι) := by
    rw [abs_div, abs_of_pos hl0p, div_lt_iff₀ hl0p]
    have := abs_nonneg u
    have : εq * (2 * Fintype.card ι) * (1 / 2) ≤ εq * (2 * Fintype.card ι) * √(L2s G σ 0) :=
      mul_le_mul_of_nonneg_left hl0 (by positivity)
    linarith
  have hQ := H ι σ c tc hσ0 hσ1 hNn hσβ hc htc hL _ hw
  rw [div_div] at hQ
  have hll : |√(L2s G σ tc) - √(L2s G σ 0)| ≤ 2 * B * |c| := by
    refine (sqrt_diff hlb.1 hl0b.1).trans ?_
    have e : L2s G σ tc - L2s G σ 0 = iteratedDeriv 2 (cgf (fun x : ℝ => x) G) tc -
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) 0 := by rw [L2s, L2s]; ring
    rw [e]
    refine (V_lip hexp ht1 h2 hW htc1).trans ?_
    have := tc_bound ha0 hexp hm h2 ht1 hV σ htc1 hL
    calc B * |tc| ≤ B * (2 * |c|) := mul_le_mul_of_nonneg_left this hB
      _ = 2 * B * |c| := by ring
  exact fin_q0 hMp hl0 hC1.le hB hQ hll

end Nd8

end P99bcb804

end X46_Nd8

section X47_Kl3

/-! R4 / Kl3 (Q6 kernel law, part 3): the canonical node kernel `κC T` is the standardised node law
`KN (T/2N) tc` for any `tc` with `sN tc > 0` (`κC_eq_KN`), hence the node quantile bound
`node_κ` in terms of `κC`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma lint_scale (h : ℝ → ℝ≥0∞) (hh : Measurable h) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, h (s * x) = ENNReal.ofReal (1 / s) * ∫⁻ v, h v := by
  have e := Real.map_volume_mul_left hs.ne'
  have h1 : ∫⁻ a, h a ∂(volume.map (fun x : ℝ => s * x)) = ∫⁻ x, h (s * x) :=
    lintegral_map hh (measurable_const_mul s)
  rw [← h1, e, lintegral_smul_measure, abs_inv, abs_of_pos hs, one_div, smul_eq_mul]

section Kl3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem κC_eq_KN (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN0 : 0 < Fintype.card ι)
    (T tc : ℝ) (hs : 0 < sN G ι σ tc) :
    κC G ι σ T = KN G ι σ (T / (2 * Fintype.card ι)) tc := by
  have hNr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN0
  have hNc : (Fintype.card ι : ℝ) * (T / (2 * Fintype.card ι)) = T / 2 := by
    field_simp
  have hff : ∀ x, ENNReal.ofReal (ffN G ι σ (T / (2 * Fintype.card ι)) tc x)
      = gE G ι σ T (sN G ι σ tc * x) := by
    intro x
    rw [ffN, ENNReal.ofReal_mul (fS_nonneg ι σ _), gE, fE, fE, hNc,
      show T / 2 + sN G ι σ tc * x / 2 = (T + sN G ι σ tc * x) / 2 by ring,
      show T / 2 - sN G ι σ tc * x / 2 = (T - sN G ι σ tc * x) / 2 by ring]
  have hZN : ENNReal.ofReal (ZN G ι σ (T / (2 * Fintype.card ι)) tc)
      = ENNReal.ofReal (1 / sN G ι σ tc) * ZE G ι σ T := by
    rw [ZN, ofReal_integral_eq_lintegral_ofReal (ffN_int ι hσ hN0 _ tc hs.ne')
      (Eventually.of_forall fun x => ffN_nonneg ι σ _ tc x), lintegral_congr hff]
    exact lint_scale (gE G ι σ T) (gE_meas_T ι σ T) hs
  have hZpos : 0 < ZN G ι σ (T / (2 * Fintype.card ι)) tc := by
    have : 0 < ENNReal.ofReal (ZN G ι σ (T / (2 * Fintype.card ι)) tc) := by
      rw [hZN]
      exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (one_div_pos.2 hs)).ne' (ZE_pos ι hσ hN0 T).ne'
    exact ENNReal.ofReal_pos.1 this
  have hc1 : ENNReal.ofReal (1 / sN G ι σ tc) * ENNReal.ofReal (sN G ι σ tc) = 1 := by
    rw [← ENNReal.ofReal_mul (one_div_pos.2 hs).le, one_div_mul_cancel hs.ne', ENNReal.ofReal_one]
  have hinv : (ENNReal.ofReal (1 / sN G ι σ tc))⁻¹ = ENNReal.ofReal (sN G ι σ tc) := by
    rw [← ENNReal.ofReal_inv_of_pos (one_div_pos.2 hs), one_div, inv_inv]
  ext B hB
  have hH : Measurable (B.indicator (fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹)) :=
    ((gE_meas_T ι σ T).mul_const _).indicator hB
  have hpt : ∀ x, ((fun x => sN G ι σ tc * x) ⁻¹' B).indicator
      (fun x => ENNReal.ofReal (hN G ι σ (T / (2 * Fintype.card ι)) tc x)) x
      = B.indicator (fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹) (sN G ι σ tc * x) *
        ENNReal.ofReal (sN G ι σ tc) := by
    intro x
    by_cases hx : sN G ι σ tc * x ∈ B
    · have hx' : x ∈ (fun x => sN G ι σ tc * x) ⁻¹' B := hx
      rw [indicator_of_mem hx', indicator_of_mem hx, hN, ENNReal.ofReal_div_of_pos hZpos, hff, hZN,
        div_eq_mul_inv, ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (one_div_pos.2 hs)).ne')
          (Or.inl ENNReal.ofReal_ne_top), hinv]
      ring
    · simp [Set.indicator, hx]
  rw [κC_apply, withDensity_apply _ hB, KN, Measure.map_apply (measurable_const_mul _) hB,
    withDensity_apply _ (measurable_const_mul _ hB), ← lintegral_indicator hB,
    ← lintegral_indicator (measurable_const_mul _ hB), lintegral_congr hpt,
    lintegral_mul_const _ (show Measurable (fun x =>
      B.indicator (fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹) (sN G ι σ tc * x))
      from hH.comp (measurable_const_mul _)),
    lint_scale _ hH hs, mul_right_comm, hc1, one_mul]

theorem node_κ (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C εq β N3 : ℝ, 0 < C ∧ 0 < εq ∧ 0 < β ∧ 1 ≤ N3 ∧
      ∀ (ι : Type) [Fintype ι] (σ T : ℝ), 0 < σ → σ ≤ 1 → N3 ≤ (Fintype.card ι : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card ι) → |T| ≤ t1 / 4 * (2 * Fintype.card ι) →
        ∀ u : ℝ, |u| < εq * (2 * Fintype.card ι) →
          |qnt (κC G ι σ T) (Phi (u / (√(L2s G σ 0) * √(2 * (Fintype.card ι : ℝ))))) - u|
            ≤ C * (1 + u ^ 2 / (2 * Fintype.card ι) + T ^ 2 / (2 * Fintype.card ι)) := by
  obtain ⟨C, εq, β, N3, hC, hεq, hβ, hN3, H⟩ :=
    node_q0 ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  refine ⟨C, εq, β, N3, hC, hεq, hβ, hN3, ?_⟩
  intro ι _ σ T hσ0 hσ1 hNn hσβ hT u hu
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := le_trans hN3 hNn
  have hNpos : 0 < Fintype.card ι := by exact_mod_cast (lt_of_lt_of_le one_pos hn1)
  have hM : 0 < 2 * (Fintype.card ι : ℝ) := by linarith
  have hn0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = T / (2 * (Fintype.card ι : ℝ)) := ⟨_, rfl⟩
  have hc : |c| ≤ t1 / 4 := by
    rw [hcd, abs_div, abs_of_pos hM, div_le_iff₀ hM]; exact hT
  obtain ⟨tc, htc1, hL, htc2⟩ := saddle ha0 hexp hm h2 ht1 hV σ (c := c) (by linarith)
  have htc : |tc| ≤ t1 / 2 := by linarith
  have hlb := L2s_bd hV hσ0 hσ1 htc1
  have hs : 0 < sN G ι σ tc := by
    unfold sN
    exact Real.sqrt_pos.2 (mul_pos hM (by linarith [hlb.1]))
  rw [κC_eq_KN ι hσ0.ne' hNpos T tc hs, ← hcd]
  have h := H ι σ c tc hσ0 hσ1 hNn hσβ hc htc hL u hu
  have e : c ^ 2 * (2 * (Fintype.card ι : ℝ)) = T ^ 2 / (2 * Fintype.card ι) := by
    rw [hcd, div_pow]; field_simp
  rw [e] at h
  exact h

end Kl3

end P99bcb804

end X47_Kl3

end P99Hyps

open MeasureTheory ProbabilityTheory in
theorem solution :
    ∀ {G : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure G] {a0 : ℝ},
      (0 : ℝ) < a0 →
        (∀ (a : ℝ), |a| ≤ a0 → MeasureTheory.Integrable (fun (x : ℝ) => Real.exp (a * x)) G) →
          ∫ (x : ℝ), x ∂G = (0 : ℝ) →
            ∀ (p m : ℝ) (v : NNReal) (F2 : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure F2],
              (0 : ℝ) < p →
                p ≤ (1 : ℝ) →
                  (0 : NNReal) < v →
                    G = ENNReal.ofReal p • ProbabilityTheory.gaussianReal m v + ENNReal.ofReal ((1 : ℝ) - p) • F2 →
                      ∀ {t1 B : ℝ},
                        (0 : ℝ) < t1 →
                          (2 : ℝ) * t1 < a0 →
                            (0 : ℝ) ≤ B →
                              (∀ (t : ℝ),
                                  |t| ≤ t1 →
                                    (1 / 2 : ℝ) ≤ iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ∧
                                      iteratedDeriv (2 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t ≤ (2 : ℝ)) →
                                (∀ t ∈ Set.Icc (-((2 : ℝ) * t1)) ((2 : ℝ) * t1),
                                    |iteratedDeriv (3 : ℕ) (ProbabilityTheory.cgf (fun (x : ℝ) => x) G) t| ≤ B) →
                                  (∀ (t : ℝ),
                                      |t| ≤ t1 →
                                        (1 / 2 : ℝ) ≤
                                          ProbabilityTheory.mgf (fun (x : ℝ) => x) (ProbabilityTheory.gaussianReal m v) t /
                                            ProbabilityTheory.mgf (fun (x : ℝ) => x) G t) →
                                    ∃ (C : ℝ) (εq : ℝ) (β : ℝ) (N3 : ℝ),
                                      (0 : ℝ) < C ∧
                                        (0 : ℝ) < εq ∧
                                          (0 : ℝ) < β ∧
                                            (1 : ℝ) ≤ N3 ∧
                                              ∀ (ι : Type) [inst : Fintype ι] (σ T : ℝ),
                                                (0 : ℝ) < σ →
                                                  σ ≤ (1 : ℝ) →
                                                    N3 ≤ ↑(Fintype.card ι) →
                                                      σ⁻¹ ≤ Real.exp (β * ↑(Fintype.card ι)) →
                                                        |T| ≤ t1 / (4 : ℝ) * ((2 : ℝ) * ↑(Fintype.card ι)) →
                                                          ∀ (u : ℝ),
                                                            |u| < εq * ((2 : ℝ) * ↑(Fintype.card ι)) →
                                                              |InfSet.sInf
                                                                      {x : ℝ |
                                                                        (ProbabilityTheory.cdf
                                                                                (ProbabilityTheory.gaussianReal (0 : ℝ)
                                                                                  (1 : NNReal)))
                                                                            (u /
                                                                              (√(iteratedDeriv (2 : ℕ)
                                                                                      (ProbabilityTheory.cgf
                                                                                        (fun (x : ℝ) => x) G)
                                                                                      (0 : ℝ) +
                                                                                    σ ^ (2 : ℕ)) *
                                                                                √((2 : ℝ) * ↑(Fintype.card ι)))) ≤
                                                                          (ProbabilityTheory.cdf
                                                                                ((ProbabilityTheory.Kernel.withDensity
                                                                                    (ProbabilityTheory.Kernel.const ℝ
                                                                                      MeasureTheory.MeasureSpace.volume)
                                                                                    fun (T d : ℝ) =>
                                                                                    ENNReal.ofReal
                                                                                          (∫ (y : ℝ),
                                                                                            ProbabilityTheory.gaussianPDFReal
                                                                                              (0 : ℝ)
                                                                                              (Real.toNNReal
                                                                                                (↑(Fintype.card ι) *
                                                                                                  σ ^ (2 : ℕ)))
                                                                                              ((T + d) / (2 : ℝ) -
                                                                                                y) ∂MeasureTheory.Measure.map
                                                                                              (fun (p : ι → ℝ) =>
                                                                                                ∑ i : ι, p i)
                                                                                              (MeasureTheory.Measure.pi
                                                                                                fun (x : ι) => G)) *
                                                                                        ENNReal.ofReal
                                                                                          (∫ (y : ℝ),
                                                                                            ProbabilityTheory.gaussianPDFReal
                                                                                              (0 : ℝ)
                                                                                              (Real.toNNReal
                                                                                                (↑(Fintype.card ι) *
                                                                                                  σ ^ (2 : ℕ)))
                                                                                              ((T - d) / (2 : ℝ) -
                                                                                                y) ∂MeasureTheory.Measure.map
                                                                                              (fun (p : ι → ℝ) =>
                                                                                                ∑ i : ι, p i)
                                                                                              (MeasureTheory.Measure.pi
                                                                                                fun (x : ι) => G)) *
                                                                                      (∫⁻ (d : ℝ),
                                                                                          ENNReal.ofReal
                                                                                              (∫ (y : ℝ),
                                                                                                ProbabilityTheory.gaussianPDFReal
                                                                                                  (0 : ℝ)
                                                                                                  (Real.toNNReal
                                                                                                    (↑(Fintype.card ι) *
                                                                                                      σ ^ (2 : ℕ)))
                                                                                                  ((T + d) / (2 : ℝ) -
                                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                                  (fun (p : ι → ℝ) =>
                                                                                                    ∑ i : ι, p i)
                                                                                                  (MeasureTheory.Measure.pi
                                                                                                    fun (x : ι) => G)) *
                                                                                            ENNReal.ofReal
                                                                                              (∫ (y : ℝ),
                                                                                                ProbabilityTheory.gaussianPDFReal
                                                                                                  (0 : ℝ)
                                                                                                  (Real.toNNReal
                                                                                                    (↑(Fintype.card ι) *
                                                                                                      σ ^ (2 : ℕ)))
                                                                                                  ((T - d) / (2 : ℝ) -
                                                                                                    y) ∂MeasureTheory.Measure.map
                                                                                                  (fun (p : ι → ℝ) =>
                                                                                                    ∑ i : ι, p i)
                                                                                                  (MeasureTheory.Measure.pi
                                                                                                    fun (x : ι) => G)))⁻¹)
                                                                                  T))
                                                                            x} -
                                                                    u| ≤
                                                                C *
                                                                  ((1 : ℝ) + u ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι)) +
                                                                    T ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι))) := by
  first
  | exact P99bcb804.node_κ
  | (intros
     apply (config := { allowSynthFailures := true }) P99bcb804.node_κ <;> assumption)
