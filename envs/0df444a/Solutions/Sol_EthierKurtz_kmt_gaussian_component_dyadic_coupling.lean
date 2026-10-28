-- Prove2me | solution 1 for EthierKurtz.kmt_gaussian_component_dyadic_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T03:08:13.368348+00:00
-- url     : https://prove2.me/submissions/71889f0c-37a0-4691-933d-5bfa3ac6d6f3

import Mathlib
import Theorems.Thm_EthierKurtz_gaussian_density_perturbation_quantile_sandwich
import Theorems.Thm_EthierKurtz_smoothed_sum_density_cramer_estimate
import Theorems.Thm_EthierKurtz_kmt_smoothed_conditional_quantile_bound

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

lemma V_zero (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) (hv : variance (fun x : ℝ => x) G = 1) :
    iteratedDeriv 2 (cgf (fun x : ℝ => x) G) 0 = 1 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) G) :=
    ioo_sub_int hexp ⟨by linarith, ha0⟩
  have hL : MemLp (fun x : ℝ => x) 2 G := memLp_of_mem_interior_integrableExpSet h0 2
  rw [variance_eq_sub hL] at hv
  rw [iteratedDeriv_two_cgf h0, deriv_cgf_zero h0]
  simp only [zero_mul, exp_zero, mul_one, mgf_zero, probReal_univ, div_one, zero_div]
  simp only [Pi.pow_apply, hm] at hv
  simp only [hm]
  linarith

lemma cum_local (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) (hv : variance (fun x : ℝ => x) G = 1) :
    ∃ t1 B : ℝ, 0 < t1 ∧ 2 * t1 < a0 ∧ 0 ≤ B ∧
      ∀ t ∈ Icc (-(2 * t1)) (2 * t1),
        (1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
          iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) ∧
        |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B := by
  have h0 : (0 : ℝ) ∈ Ioo (-a0) a0 := ⟨by linarith, ha0⟩
  have hc : ContinuousAt (iteratedDeriv 2 (cgf (fun x : ℝ => x) G)) 0 :=
    (an_cgf hexp 2 0 h0).continuousAt
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  have hKs : Icc (-(a0 / 2)) (a0 / 2) ⊆ Ioo (-a0) a0 := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(a0 / 2)) (b := a0 / 2)).exists_bound_of_continuousOn
    ((an_cgf hexp 3).continuousOn.mono hKs)
  refine ⟨min δ a0 / 4, max C 0, by positivity, ?_, le_max_right _ _, ?_⟩
  · have := min_le_right δ a0; linarith
  intro t ht
  have hm1 := min_le_left δ a0
  have hm2 := min_le_right δ a0
  have hta : |t| ≤ min δ a0 / 2 := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hmpos : 0 < min δ a0 := lt_min hδ ha0
  refine ⟨?_, ?_⟩
  · have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith
    have := hδc hd
    rw [Real.dist_eq, V_zero ha0 hexp hm hv] at this
    have := abs_lt.1 this
    constructor <;> linarith [this.1, this.2]
  · have hx : t ∈ Icc (-(a0 / 2)) (a0 / 2) := ⟨by linarith [(abs_le.1 hta).1],
      by linarith [(abs_le.1 hta).2]⟩
    have := hC t hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

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

section X6_Cg2

/-! R4 / Q3: the tilted law of a Gaussian-component mixture keeps a Gaussian component.
* `cf_tilt`: `charFun (G.tilted (t·)) s = complexMGF id G (t + s i) / mgf id G t`;
* `cmgf_mix`, `mgf_mix`: (complex) mgf of `p•N + (1-p)•F2` is the mixture of the mgfs;
* `norm_cf_tilt_mix`: `‖charFun G_t s‖ ≤ p_t e^{-v s²/2} + (1 - p_t)`, `p_t = p M_N(t)/M_G(t)`;
* `norm_cf_shift`: centring does not change `‖charFun‖`;
* `pt_lower_g`: `p_t ≥ p/2` for `|t| ≤ t2`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Mix

variable (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N F2 : Measure ℝ) [IsProbabilityMeasure N]
  [IsProbabilityMeasure F2]

end Mix

lemma pt_lower_g {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ} (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) (m : ℝ) (v : ℝ≥0) :
    ∃ t2 : ℝ, 0 < t2 ∧ ∀ t : ℝ, |t| ≤ t2 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) G) :=
    ioo_sub_int hexp ⟨by linarith, ha0⟩
  have hcG : ContinuousAt (mgf (fun x : ℝ => x) G) 0 :=
    continuousOn_mgf.continuousAt (isOpen_interior.mem_nhds h0)
  have hcN : Continuous (mgf (fun x : ℝ => x) (gaussianReal m v)) := by
    have : mgf (fun x : ℝ => x) (gaussianReal m v) = fun t => exp (m * t + v * t ^ 2 / 2) :=
      mgf_id_gaussianReal
    rw [this]; fun_prop
  have hG0 : mgf (fun x : ℝ => x) G 0 = 1 := by simp [mgf_zero]
  have hN0 : mgf (fun x : ℝ => x) (gaussianReal m v) 0 = 1 := by simp [mgf_zero]
  have hc : ContinuousAt (fun t => mgf (fun x : ℝ => x) (gaussianReal m v) t
      / mgf (fun x : ℝ => x) G t) 0 :=
    hcN.continuousAt.div hcG (by rw [hG0]; norm_num)
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hc (1 / 2) (by norm_num)
  refine ⟨δ / 2, by positivity, fun t ht => ?_⟩
  have hd : dist t 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith
  have := hδc hd
  rw [Real.dist_eq, hG0, hN0, div_one] at this
  linarith [(abs_lt.1 this).1]

end P99bcb804

end X6_Cg2

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
noncomputable def L2s (G : Measure ℝ) (σ t : ℝ) : ℝ :=
  iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t + σ ^ 2

section Cr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma tmu_zero (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) : tmu G 0 = 0 := by
  rw [tmu, deriv_cgf_zero (mem_int_of hexp (by simpa using ha0))]
  simp [hm]

end Cr3

end P99bcb804

end X11_Cr3

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

section X15_Kr1

/-! R4 / Kr1 (root, single factor): pointwise local Cramér for the smoothed sum density
`fS(Nδ) ≈ φ_{N L2s 0}(0) e^{-Nδ²/(2 L2s 0)}` with relative error `e^{±K(1/√N + |δ| + N|δ|³)}`
(`near_single`, the one-factor analogue of `near_ratio`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Kr1

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem near_single :
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
                                            ∀ (ι : Type) [inst : Fintype ι] (σ δ : ℝ),
                                              (0 : ℝ) < σ →
                                                σ ≤ (1 : ℝ) →
                                                  N1 ≤ ↑(Fintype.card ι) →
                                                    (2 : ℕ) ≤ Fintype.card ι →
                                                      ((1 : ℝ) - κ') ^ (Fintype.card ι - (1 : ℕ)) / σ ≤
                                                          (1 : ℝ) / ↑(Fintype.card ι) →
                                                        |δ| ≤ t1 / (2 : ℝ) →
                                                          (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(P99bcb804.L2s G σ (0 : ℝ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) * P99bcb804.L2s G σ (0 : ℝ)))) *
                                                                Real.exp
                                                                  (-(K *
                                                                      ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                        ↑(Fintype.card ι) * |δ| ^ (3 : ℕ)))) ≤
                                                              P99bcb804.fS G ι σ (↑(Fintype.card ι) * δ) ∧
                                                            P99bcb804.fS G ι σ (↑(Fintype.card ι) * δ) ≤
                                                              (√((2 : ℝ) * Real.pi * ↑(Fintype.card ι)))⁻¹ *
                                                                    (√(P99bcb804.L2s G σ (0 : ℝ)))⁻¹ *
                                                                  Real.exp
                                                                    (-(↑(Fintype.card ι) * δ ^ (2 : ℕ) /
                                                                        ((2 : ℝ) * P99bcb804.L2s G σ (0 : ℝ)))) *
                                                                Real.exp
                                                                  (K *
                                                                    ((1 : ℝ) / √↑(Fintype.card ι) + |δ| +
                                                                      ↑(Fintype.card ι) * |δ| ^ (3 : ℕ))) := EthierKurtz.smoothed_sum_density_cramer_estimate

end Kr1

end P99bcb804

end X15_Kr1

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

end Nd3

end P99bcb804

end X16_Nd3

section X17_Kl1

/-! R4 / Kl1 (Q6 kernel law, part 1): the smoothed sum law `sL G ι σ = (law of Σ_ι X_i) ∗ N(0, Nσ²)`,
`sL_dens` (density `fS`), `sL_sum` (`sL (ι ⊕ ι) = sL ι ∗ sL ι`), and the rotation substitution
`lint_rot`: `∫∫ F(s1+s2, s1-s2) = (1/2) ∫∫ F(T,d)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sumL (G : Measure ℝ) (ι : Type) [Fintype ι] : Measure ℝ :=
  (Measure.pi fun _ : ι => G).map (fun p => ∑ i, p i)

noncomputable def sL (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : Measure ℝ :=
  sumL G ι ∗ gaussianReal 0 (Fintype.card ι * σ ^ 2).toNNReal

lemma lint_half (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ s, h (2 * s) = ENNReal.ofReal (1 / 2) * ∫⁻ v, h v := by
  have e := Real.map_volume_mul_left (a := 2) (by norm_num)
  have h1 : ∫⁻ a, h a ∂(volume.map (fun x : ℝ => 2 * x)) = ∫⁻ s, h (2 * s) :=
    lintegral_map hh (measurable_const_mul 2)
  rw [← h1, e, lintegral_smul_measure]
  norm_num

lemma lint_rot (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ s1, ∫⁻ s2, F (s1 + s2, s1 - s2) = ENNReal.ofReal (1 / 2) * ∫⁻ T, ∫⁻ d, F (T, d) := by
  have step1 : ∀ s1 : ℝ, ∫⁻ s2, F (s1 + s2, s1 - s2) = ∫⁻ u, F (u, 2 * s1 - u) := by
    intro s1
    have := lintegral_add_left_eq_self (μ := volume) (fun u => F (u, 2 * s1 - u)) s1
    rw [← this]
    congr 1
    funext s2
    congr 2
    ring
  simp_rw [step1]
  have hm : Measurable (fun p : ℝ × ℝ => F (p.2, 2 * p.1 - p.2)) := hF.comp (by fun_prop)
  rw [lintegral_lintegral_swap (f := fun s1 u => F (u, 2 * s1 - u)) hm.aemeasurable]
  have step2 : ∀ u : ℝ, ∫⁻ s1, F (u, 2 * s1 - u) = ENNReal.ofReal (1 / 2) * ∫⁻ d, F (u, d) := by
    intro u
    have h2 := lint_half (fun v => F (u, v - u)) (hF.comp (by fun_prop))
    try simp only at h2
    rw [h2]
    congr 1
    exact lintegral_sub_right_eq_self (fun d => F (u, d)) u
  simp_rw [step2]
  exact lintegral_const_mul _ hF.lintegral_prod_right'

section Kl1

variable {G : Measure ℝ} [IsProbabilityMeasure G]

instance sumL_prob (ι : Type) [Fintype ι] : IsProbabilityMeasure (sumL G ι) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

instance sL_prob (ι : Type) [Fintype ι] (σ : ℝ) : IsProbabilityMeasure (sL G ι σ) := by
  unfold sL; infer_instance

lemma sL_dens (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    sL G ι σ = volume.withDensity (fun a => ENNReal.ofReal (fS G ι σ a)) := by
  have hv : (Fintype.card ι * σ ^ 2).toNNReal ≠ 0 := by
    have : 0 < (Fintype.card ι : ℝ) * σ ^ 2 := by
      have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
      positivity
    exact (Real.toNNReal_pos.2 this).ne'
  rw [sL, conv_gauss_eq _ hv]
  congr 1
  funext a
  rw [lint_dens]
  rfl

lemma sumL_sum (ι : Type) [Fintype ι] : sumL G (ι ⊕ ι) = sumL G ι ∗ sumL G ι := by
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => G)
  have hs : Measurable (fun p : ι → ℝ => ∑ i, p i) := by fun_prop
  simp only [sumL, Measure.conv]
  rw [Measure.map_prod_map _ _ hs hs, Measure.map_map (by fun_prop) (hs.prodMap hs),
    ← hmp.map_eq, Measure.map_map (by fun_prop) hmp.measurable]
  congr 1
  funext p
  simp [Fintype.sum_sum_type, MeasurableEquiv.sumPiEquivProdPi]

lemma conv4 (A g : Measure ℝ) [IsProbabilityMeasure A] [IsProbabilityMeasure g] :
    (A ∗ g) ∗ (A ∗ g) = (A ∗ A) ∗ (g ∗ g) := by
  rw [Measure.conv_assoc, ← Measure.conv_assoc g A g, Measure.conv_comm g A,
    Measure.conv_assoc A g g, ← Measure.conv_assoc A A]

lemma sL_sum (ι : Type) [Fintype ι] (σ : ℝ) : sL G (ι ⊕ ι) σ = sL G ι σ ∗ sL G ι σ := by
  have h0 : 0 ≤ (Fintype.card ι : ℝ) * σ ^ 2 := by positivity
  have hv : ((Fintype.card ι : ℝ) * σ ^ 2).toNNReal + ((Fintype.card ι : ℝ) * σ ^ 2).toNNReal
      = ((Fintype.card (ι ⊕ ι) : ℝ) * σ ^ 2).toNNReal := by
    rw [← Real.toNNReal_add h0 h0, Fintype.card_sum]
    congr 1
    push_cast
    ring
  rw [sL, sL, conv4, gaussianReal_conv_gaussianReal, hv, add_zero, sumL_sum]

end Kl1

end P99bcb804

end X17_Kl1

section X18_Nd4

/-! R4 / Nd4 (Q5 node, far region): `far_exp` (∫ of e^{-a|x|} off [-r,r]), `kappa_cond`
(`σ⁻¹ ≤ e^{κN/2}` gives the LCLT error condition), `far_pt` (two-sided Chernoff bound for the
product `fS(Nc + d/2) fS(Nc - d/2)`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Nd4

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

lemma hasDerivAt_phi (t : ℝ) : HasDerivAt phi (-t * phi t) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 2)) (-t) t := by
    exact ((hasDerivAt_pow 2 t).div_const 2).neg.congr_deriv (by norm_num)
  have h2 := (h1.exp).const_mul (√(2 * π))⁻¹
  show HasDerivAt (fun t => (√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)))
    (-t * ((√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)))) t
  exact h2.congr_deriv (by ring)

lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

lemma tendsto_phi_atTop : Tendsto phi atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => -(t ^ 2 / 2)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos)
  have := (Real.tendsto_exp_atBot.comp h).const_mul (√(2 * π))⁻¹
  rw [mul_zero] at this
  exact this

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

/-- `∫_x^∞ t φ(t) dt = φ(x)` for `x ≥ 0`, with integrability. -/
lemma integral_Ioi_mul_phi {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t => t * phi t) (Ioi x) ∧ ∫ t in Ioi x, t * phi t = phi x := by
  have hd : ∀ t ∈ Ioi x, HasDerivAt (fun t => -phi t) (t * phi t) t := by
    intro t _
    exact (hasDerivAt_phi t).neg.congr_deriv (by ring)
  have hc : ContinuousWithinAt (fun t => -phi t) (Ici x) x :=
    (continuous_phi.neg).continuousAt.continuousWithinAt
  have hpos : ∀ t ∈ Ioi x, 0 ≤ t * phi t := fun t ht =>
    mul_nonneg (hx.trans (le_of_lt ht)) (phi_pos t).le
  have hlim : Tendsto (fun t => -phi t) atTop (𝓝 0) := by
    simpa using tendsto_phi_atTop.neg
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hpos hlim, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hc hd hpos hlim]
  ring

/-- Mills ratio, upper bound: `1 - Φ(x) ≤ φ(x)/x` for `x > 0`. -/
lemma mills_upper {x : ℝ} (hx : 0 < x) : 1 - cdf (gaussianReal 0 1) x ≤ phi x / x := by
  obtain ⟨hint, heq⟩ := integral_Ioi_mul_phi hx.le
  rw [one_sub_cdf_std, le_div_iff₀ hx, ← heq, ← integral_mul_const]
  refine setIntegral_mono_on (integrable_phi.integrableOn.mul_const x) hint measurableSet_Ioi
    (fun t ht => ?_)
  have : x ≤ t := le_of_lt ht
  nlinarith [phi_pos t]

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

lemma continuous_cdf_std : Continuous (fun y => cdf (gaussianReal 0 1) y) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_cdf_std x).continuousAt

/-- Symmetry: `Φ(-x) = 1 - Φ(x)`. -/
lemma cdf_std_neg (x : ℝ) : cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  rw [cdf_std_eq, one_sub_cdf_std]
  have : ∫ t in Iic (-x), phi t = ∫ t in Iic (-x), phi (-t) := by
    simp_rw [phi_neg]
  rw [this, integral_comp_neg_Iic, neg_neg]

/-- Lower-tail Mills bound: `Φ(x) ≤ φ(x)/(-x)` for `x < 0`. -/
lemma mills_upper_neg {x : ℝ} (hx : x < 0) : cdf (gaussianReal 0 1) x ≤ phi x / (-x) := by
  have h := mills_upper (x := -x) (by linarith)
  rw [cdf_std_neg, phi_neg] at h
  linarith

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

/-- `Φ/φ` (lower Mills ratio). -/
noncomputable def Qm (w : ℝ) : ℝ := Phi w / phi w

/-- `(1-Φ)/φ` (upper Mills ratio). -/
noncomputable def Rm (w : ℝ) : ℝ := (1 - Phi w) / phi w

lemma Rm_eq_Qm_neg (w : ℝ) : Rm w = Qm (-w) := by
  simp only [Rm, Qm, Phi, cdf_std_neg, phi_neg]

lemma Qm_nonneg (w : ℝ) : 0 ≤ Qm w :=
  div_nonneg (cdf_nonneg _ _) (phi_pos w).le

lemma Rm_nonneg (w : ℝ) : 0 ≤ Rm w := by
  rw [Rm_eq_Qm_neg]; exact Qm_nonneg _

lemma hasDerivAt_Qm (w : ℝ) : HasDerivAt Qm (1 + w * Qm w) w := by
  have := (hasDerivAt_cdf_std w).div (hasDerivAt_phi w) (phi_pos w).ne'
  refine this.congr_deriv ?_
  have hp := (phi_pos w).ne'
  simp only [Qm, Phi]
  field_simp
  ring

/-- `-w Φ(w)/φ(w) ≤ 1` for `w < 0`. -/
lemma neg_mul_Qm_le {w : ℝ} (hw : w < 0) : -w * Qm w ≤ 1 := by
  have h := mills_upper_neg hw
  have hp := phi_pos w
  unfold Qm Phi
  rw [le_div_iff₀ (by linarith)] at h
  rw [mul_div_assoc', div_le_one hp]
  linarith

/-- `w (1-Φ(w))/φ(w) ≤ 1` for `w > 0`. -/
lemma mul_Rm_le {w : ℝ} (hw : 0 < w) : w * Rm w ≤ 1 := by
  rw [Rm_eq_Qm_neg]
  have := neg_mul_Qm_le (w := -w) (by linarith)
  simpa using this

lemma one_add_mul_Qm_nonneg (w : ℝ) : 0 ≤ 1 + w * Qm w := by
  rcases lt_or_ge w 0 with hw | hw
  · have := neg_mul_Qm_le hw; linarith
  · have := Qm_nonneg w; nlinarith

lemma Qm_monotone : Monotone Qm :=
  monotone_of_deriv_nonneg (fun w => (hasDerivAt_Qm w).differentiableAt)
    (fun w => by rw [(hasDerivAt_Qm w).deriv]; exact one_add_mul_Qm_nonneg w)

lemma Rm_antitone : Antitone Rm := by
  intro a b hab
  rw [Rm_eq_Qm_neg, Rm_eq_Qm_neg]
  exact Qm_monotone (by linarith)

lemma hasDerivAt_Rm (w : ℝ) : HasDerivAt Rm (w * Rm w - 1) w := by
  have h : Rm = fun w => Qm (-w) := funext Rm_eq_Qm_neg
  rw [h]
  have := (hasDerivAt_Qm (-w)).comp w (hasDerivAt_neg w)
  refine this.congr_deriv ?_
  simp only
  ring

lemma Qm_zero_eq_Rm_zero : Rm 0 = Qm 0 := by
  rw [Rm_eq_Qm_neg, neg_zero]

lemma Phi_mul_Rm (z : ℝ) : Phi z * Rm z = (1 - Phi z) * Qm z := by
  simp only [Rm, Qm]; ring

/-! ## Child C (Tusnády quantile inequality), generic over the family of sum laws. -/

lemma hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (phi x) x := hasDerivAt_cdf_std x

lemma continuous_Phi' : Continuous Phi := continuous_cdf_std

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

lemma fS_aff_int (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι)
    (a k : ℝ) (hk : k ≠ 0) : Integrable (fun x => fS G ι σ (a + k * x)) := by
  have h1 : Integrable (fun y => fS G ι σ (y + a)) := (fS_integrable ι hσ hN).1.comp_add_right a
  have h2 := h1.comp_mul_left' hk
  refine h2.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [add_comm]

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

def rotM (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + p.2, p.1 - p.2)

lemma measurable_rotM : Measurable rotM := by unfold rotM; fun_prop

noncomputable def ρC (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : Measure (ℝ × ℝ) :=
  ((sL G ι σ).prod (sL G ι σ)).map rotM

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

lemma ZE_lt_top (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) (T : ℝ) :
    ZE G ι σ T < ∞ := by
  have hint := fS_aff_int (G := G) ι hσ hN (T / 2) (1 / 2) (by norm_num)
  have hlt := hint.lintegral_lt_top
  set Cb := (√(2 * π * (Fintype.card ι * σ ^ 2)))⁻¹
  have hle : ∀ d, gE G ι σ T d ≤ ENNReal.ofReal Cb * ENNReal.ofReal (fS G ι σ (T / 2 + 1 / 2 * d)) := by
    intro d
    unfold gE fE
    rw [mul_comm (ENNReal.ofReal Cb), show (T + d) / 2 = T / 2 + 1 / 2 * d by ring]
    gcongr
    exact fS_le ι σ _
  calc ZE G ι σ T ≤ ∫⁻ d, ENNReal.ofReal Cb * ENNReal.ofReal (fS G ι σ (T / 2 + 1 / 2 * d)) :=
        lintegral_mono hle
    _ = ENNReal.ofReal Cb * ∫⁻ d, ENNReal.ofReal (fS G ι σ (T / 2 + 1 / 2 * d)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt

instance κC_markov (ι : Type) [Fintype ι] {σ : ℝ} [Fact (σ ≠ 0)] [Fact (0 < Fintype.card ι)] :
    IsMarkovKernel (κC G ι σ) := by
  have hσ : σ ≠ 0 := Fact.out
  have hN : 0 < Fintype.card ι := Fact.out
  refine ⟨fun T => ⟨?_⟩⟩
  rw [κC, Kernel.withDensity_apply _ (dens_meas ι σ), withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, Kernel.const_apply,
    lintegral_mul_const _ (gE_meas_T ι σ T)]
  exact ENNReal.mul_inv_cancel (ZE_pos ι hσ hN T).ne' (ZE_lt_top ι hσ hN T).ne

lemma κC_apply (ι : Type) [Fintype ι] (σ T : ℝ) :
    κC G ι σ T = volume.withDensity (fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹) := by
  rw [κC, Kernel.withDensity_apply _ (dens_meas ι σ), Kernel.const_apply]

lemma sL_dens' (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    sL G ι σ = volume.withDensity (fE G ι σ) := by
  rw [sL_dens ι hσ hN]; rfl

lemma rho_lint (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι)
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂(ρC G ι σ) = ENNReal.ofReal (1 / 2) * ∫⁻ T, ∫⁻ d, F (T, d) * gE G ι σ T d := by
  have hfE := fE_meas (G := G) ι σ
  have hH : Measurable (fun z : ℝ × ℝ => F (rotM z)) := hF.comp measurable_rotM
  have hFg : Measurable (fun p : ℝ × ℝ => F p * gE G ι σ p.1 p.2) := hF.mul (gE_meas ι σ)
  calc ∫⁻ z, F z ∂(ρC G ι σ)
      = ∫⁻ z, F (rotM z) ∂((sL G ι σ).prod (sL G ι σ)) := lintegral_map hF measurable_rotM
    _ = ∫⁻ x, ∫⁻ y, F (rotM (x, y)) ∂(sL G ι σ) ∂(sL G ι σ) := lintegral_prod _ hH.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, F (rotM (x, y)) ∂(volume.withDensity (fE G ι σ))
          ∂(volume.withDensity (fE G ι σ)) := by rw [sL_dens' ι hσ hN]
    _ = ∫⁻ x, fE G ι σ x * ∫⁻ y, fE G ι σ y * F (rotM (x, y)) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hfE
          (show Measurable (fun x => ∫⁻ y, F (rotM (x, y)) ∂(volume.withDensity (fE G ι σ)))
            from hH.lintegral_prod_right')]
        refine lintegral_congr fun x => ?_
        simp only [Pi.mul_apply]
        rw [lintegral_withDensity_eq_lintegral_mul _ hfE
          (show Measurable (fun y => F (rotM (x, y))) from hH.comp measurable_prodMk_left)]
        rfl
    _ = ∫⁻ s1, ∫⁻ s2, (fun p : ℝ × ℝ => F p * gE G ι σ p.1 p.2) (s1 + s2, s1 - s2) := by
        refine lintegral_congr fun x => ?_
        rw [← lintegral_const_mul _ (show Measurable (fun y => fE G ι σ y * F (rotM (x, y)))
          from hfE.mul (hH.comp measurable_prodMk_left))]
        refine lintegral_congr fun y => ?_
        simp only [rotM, gE]
        rw [show (x + y + (x - y)) / 2 = x by ring, show (x + y - (x - y)) / 2 = y by ring]
        ring
    _ = ENNReal.ofReal (1 / 2) * ∫⁻ T, ∫⁻ d, F (T, d) * gE G ι σ T d := lint_rot _ hFg

lemma sL_fst (ι : Type) [Fintype ι] (σ : ℝ) : sL G (ι ⊕ ι) σ = (ρC G ι σ).map Prod.fst := by
  rw [sL_sum, ρC, Measure.map_map measurable_fst measurable_rotM]
  rfl

lemma fst_dens (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    sL G (ι ⊕ ι) σ = volume.withDensity (fun T => ENNReal.ofReal (1 / 2) * ZE G ι σ T) := by
  ext A hA
  have hA1 : MeasurableSet (Prod.fst ⁻¹' A : Set (ℝ × ℝ)) := measurable_fst hA
  have hI : Measurable ((Prod.fst ⁻¹' A : Set (ℝ × ℝ)).indicator (1 : ℝ × ℝ → ℝ≥0∞)) :=
    measurable_one.indicator hA1
  rw [withDensity_apply _ hA, sL_fst, Measure.map_apply measurable_fst hA,
    ← lintegral_indicator_one hA1, rho_lint ι hσ hN _ hI, ← lintegral_indicator hA,
    ← lintegral_const_mul _ (show Measurable (fun T => ∫⁻ d,
      (Prod.fst ⁻¹' A : Set (ℝ × ℝ)).indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d) * gE G ι σ T d)
      from (hI.mul (gE_meas ι σ)).lintegral_prod_right')]
  refine lintegral_congr fun T => ?_
  by_cases hT : T ∈ A
  · simp [hT, Set.indicator, ZE]
  · simp [hT, Set.indicator]

theorem disint (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι) :
    ρC G ι σ = (sL G (ι ⊕ ι) σ) ⊗ₘ κC G ι σ := by
  haveI : Fact (σ ≠ 0) := ⟨hσ⟩
  haveI : Fact (0 < Fintype.card ι) := ⟨hN⟩
  ext S hS
  have hI : Measurable (S.indicator (1 : ℝ × ℝ → ℝ≥0∞)) := measurable_one.indicator hS
  rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, rho_lint ι hσ hN _ hI,
    Measure.lintegral_compProd hI, fst_dens ι hσ hN,
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun T => ENNReal.ofReal (1 / 2) * ZE G ι σ T)
        from measurable_const.mul (ZE_meas ι σ))
      (show Measurable (fun a => ∫⁻ b, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (a, b) ∂(κC G ι σ a))
        from hI.lintegral_kernel_prod_right'),
    ← lintegral_const_mul _ (show Measurable (fun T => ∫⁻ d,
      S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d) * gE G ι σ T d)
      from (hI.mul (gE_meas ι σ)).lintegral_prod_right')]
  refine lintegral_congr fun T => ?_
  have hZ0 := (ZE_pos (G := G) ι hσ hN T).ne'
  have hZt := (ZE_lt_top (G := G) ι hσ hN T).ne
  have hm : Measurable (fun d => S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d)) :=
    hI.comp measurable_prodMk_left
  rw [Pi.mul_apply, κC_apply, lintegral_withDensity_eq_lintegral_mul _
    ((gE_meas_T ι σ T).mul_const _) hm]
  have e : ∫⁻ d, ((fun d => gE G ι σ T d * (ZE G ι σ T)⁻¹) * fun d =>
      S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d)) d
      = (ZE G ι σ T)⁻¹ * ∫⁻ d, S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d) * gE G ι σ T d := by
    rw [← lintegral_const_mul _ (show Measurable (fun d =>
      S.indicator (1 : ℝ × ℝ → ℝ≥0∞) (T, d) * gE G ι σ T d) from hm.mul (gE_meas_T ι σ T))]
    refine lintegral_congr fun d => ?_
    simp only [Pi.mul_apply]
    ring
  rw [e, ← mul_assoc, mul_assoc (ENNReal.ofReal (1 / 2)), ENNReal.mul_inv_cancel hZ0 hZt, mul_one]

end Kl2

end P99bcb804

end X24_Kl2

section X30_DtG

/-! R4 / DtG: bridge from the density hypotheses `DtHyp` (at `ε = 1/√m`) to the Tusnady sandwich
for the law `L = (volume.withDensity h).map (√m * ·)` via `tusnady_one`. -/

open MeasureTheory ProbabilityTheory Real Set Filter

namespace P99bcb804

lemma dens_real {h : ℝ → ℝ} (hh0 : ∀ x, 0 ≤ h x) (hint : Integrable h) {S : Set ℝ}
    (hS : MeasurableSet S) :
    (volume.withDensity (fun x => ENNReal.ofReal (h x))).real S = ∫ x in S, h x := by
  rw [measureReal_def, withDensity_apply _ hS,
    ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn (Eventually.of_forall fun x => hh0 x),
    ENNReal.toReal_ofReal (setIntegral_nonneg hS (fun x _ => hh0 x))]

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

section X33_Stein

/-! Stein solution layer for 99bcb804 (copied from _be.lean). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal

namespace P99bcb804

/-- Stein solution `f_z` of `f' - w f = 1{w ≤ z} - Φ(z)`. -/
noncomputable def steinF (z w : ℝ) : ℝ :=
  if w ≤ z then (1 - Phi z) * Qm w else Phi z * Rm w

lemma Phi_nonneg (z : ℝ) : 0 ≤ Phi z := cdf_nonneg _ _
lemma Phi_le_one (z : ℝ) : Phi z ≤ 1 := cdf_le_one _ _

lemma steinF_nonneg (z w : ℝ) : 0 ≤ steinF z w := by
  unfold steinF
  have := Phi_le_one z
  split_ifs
  · exact mul_nonneg (by linarith) (Qm_nonneg w)
  · exact mul_nonneg (Phi_nonneg z) (Rm_nonneg w)

/-- The diagonal value `Φ(z)(1-Φ(z))/φ(z)` is at most `Q(0) = √(2π)/2`. -/
lemma diag_le (z : ℝ) : (1 - Phi z) * Qm z ≤ Qm 0 := by
  have h1 := Phi_le_one z
  have h0 := Phi_nonneg z
  rcases le_or_gt z 0 with hz | hz
  · have := Qm_monotone hz
    have := Qm_nonneg z
    nlinarith
  · rw [← Phi_mul_Rm, ← Qm_zero_eq_Rm_zero]
    have := Rm_antitone hz.le
    have := Rm_nonneg z
    nlinarith

lemma steinF_le (z w : ℝ) : steinF z w ≤ Qm 0 := by
  unfold steinF
  have h1 := Phi_le_one z
  have h0 := Phi_nonneg z
  split_ifs with hw
  · have := Qm_monotone hw
    have := diag_le z
    nlinarith
  · have := Rm_antitone (le_of_lt (not_le.mp hw))
    have := diag_le z
    rw [← Phi_mul_Rm] at this
    nlinarith

lemma deriv1_bound {z w : ℝ} (hw : w ≤ z) :
    0 ≤ (1 - Phi z) * (1 + w * Qm w) ∧ (1 - Phi z) * (1 + w * Qm w) ≤ 1 := by
  have h1 := Phi_le_one z
  have hq := Qm_nonneg w
  have hn := one_add_mul_Qm_nonneg w
  refine ⟨mul_nonneg (by linarith) hn, ?_⟩
  rcases lt_or_ge w 0 with hw0 | hw0
  · have : w * Qm w ≤ 0 := by nlinarith
    have := Phi_nonneg z
    nlinarith
  · have hPhi : Phi w ≤ Phi z := monotone_cdf _ hw
    have e := Phi_mul_Rm w
    have hw1 := Phi_le_one w
    have hw2 := Phi_nonneg w
    have hR : w * Rm w ≤ 1 := by
      rcases eq_or_lt_of_le hw0 with h | h
      · rw [← h]; simp
      · exact mul_Rm_le h
    have hr := Rm_nonneg w
    -- (1-Φz)(1+wQ) ≤ (1-Φw)(1+wQ) = (1-Φw) + w Φw Rw ≤ 1
    have step : (1 - Phi z) * (1 + w * Qm w) ≤ (1 - Phi w) * (1 + w * Qm w) :=
      mul_le_mul_of_nonneg_right (by linarith) hn
    have : (1 - Phi w) * (1 + w * Qm w) = (1 - Phi w) + Phi w * (w * Rm w) := by
      have : (1 - Phi w) * (w * Qm w) = Phi w * (w * Rm w) := by
        rw [show (1 - Phi w) * (w * Qm w) = w * ((1 - Phi w) * Qm w) by ring, ← e]; ring
      linarith [this]
    nlinarith

lemma deriv2_bound {z w : ℝ} (hw : z ≤ w) :
    -1 ≤ Phi z * (w * Rm w - 1) ∧ Phi z * (w * Rm w - 1) ≤ 0 := by
  have h0 := Phi_nonneg z
  have h1 := Phi_le_one z
  have hr := Rm_nonneg w
  have hR : w * Rm w ≤ 1 := by
    rcases lt_or_ge 0 w with h | h
    · exact mul_Rm_le h
    · nlinarith
  refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos h0 (by linarith)⟩
  rcases lt_or_ge w 0 with hw0 | hw0
  · have hPhi : Phi z ≤ Phi w := monotone_cdf _ hw
    have e := Phi_mul_Rm w
    have hq := neg_mul_Qm_le hw0
    have hq0 := Qm_nonneg w
    have hw1 := Phi_le_one w
    have hw2 := Phi_nonneg w
    have hpos : 0 ≤ 1 - w * Rm w := by linarith
    have step : Phi z * (1 - w * Rm w) ≤ Phi w * (1 - w * Rm w) :=
      mul_le_mul_of_nonneg_right hPhi hpos
    have : Phi w * (1 - w * Rm w) = Phi w + (-w * Qm w) * (1 - Phi w) := by
      have : Phi w * (w * Rm w) = w * ((1 - Phi w) * Qm w) := by rw [← e]; ring
      linarith [this]
    linarith [mul_le_mul_of_nonneg_right hq (show 0 ≤ 1 - Phi w by linarith)]
  · nlinarith [mul_nonneg hw0 hr]

lemma hasDerivAt_Qm_branch (z w : ℝ) :
    HasDerivAt (fun w => (1 - Phi z) * Qm w) ((1 - Phi z) * (1 + w * Qm w)) w :=
  (hasDerivAt_Qm w).const_mul _

lemma hasDerivAt_Rm_branch (z w : ℝ) :
    HasDerivAt (fun w => Phi z * Rm w) (Phi z * (w * Rm w - 1)) w :=
  (hasDerivAt_Rm w).const_mul _

/-- The Stein solution is 1-Lipschitz. -/
lemma steinF_lip (z a b : ℝ) : |steinF z a - steinF z b| ≤ |a - b| := by
  -- Lipschitz on each closed half-line, then glue at `z`.
  have L1 : ∀ a b, a ≤ z → b ≤ z → |steinF z a - steinF z b| ≤ |a - b| := by
    intro a b ha hb
    have hfa : steinF z a = (1 - Phi z) * Qm a := by simp [steinF, ha]
    have hfb : steinF z b = (1 - Phi z) * Qm b := by simp [steinF, hb]
    rw [hfa, hfb]
    have := (convex_Iic z).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => (1 - Phi z) * Qm w) (f' := fun w => (1 - Phi z) * (1 + w * Qm w)) (C := 1)
      (fun x _ => (hasDerivAt_Qm_branch z x).hasDerivWithinAt)
      (fun x hx => by
        obtain ⟨h0, h1⟩ := deriv1_bound (z := z) (w := x) hx
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
      hb ha
    simpa [Real.norm_eq_abs] using this
  have L2 : ∀ a b, z ≤ a → z ≤ b → |steinF z a - steinF z b| ≤ |a - b| := by
    intro a b ha hb
    have hfa : steinF z a = Phi z * Rm a := by
      rcases eq_or_lt_of_le ha with h | h
      · subst h; simp [steinF, Phi_mul_Rm]
      · simp [steinF, not_le.mpr h]
    have hfb : steinF z b = Phi z * Rm b := by
      rcases eq_or_lt_of_le hb with h | h
      · subst h; simp [steinF, Phi_mul_Rm]
      · simp [steinF, not_le.mpr h]
    rw [hfa, hfb]
    have := (convex_Ici z).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun w => Phi z * Rm w) (f' := fun w => Phi z * (w * Rm w - 1)) (C := 1)
      (fun x _ => (hasDerivAt_Rm_branch z x).hasDerivWithinAt)
      (fun x hx => by
        obtain ⟨h0, h1⟩ := deriv2_bound (z := z) (w := x) hx
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
      hb ha
    simpa [Real.norm_eq_abs] using this
  rcases le_total a z with ha | ha <;> rcases le_total b z with hb | hb
  · exact L1 a b ha hb
  · calc |steinF z a - steinF z b| ≤ |steinF z a - steinF z z| + |steinF z z - steinF z b| :=
          abs_sub_le _ _ _
      _ ≤ |a - z| + |z - b| := add_le_add (L1 a z ha le_rfl) (L2 z b le_rfl hb)
      _ = |a - b| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          ring
  · calc |steinF z a - steinF z b| ≤ |steinF z a - steinF z z| + |steinF z z - steinF z b| :=
          abs_sub_le _ _ _
      _ ≤ |a - z| + |z - b| := add_le_add (L2 a z ha le_rfl) (L1 z b le_rfl hb)
      _ = |a - b| := by
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          ring
  · exact L2 a b ha hb

lemma continuous_steinF (z : ℝ) : Continuous (steinF z) := by
  refine Metric.continuous_iff.mpr fun b ε hε => ⟨ε, hε, fun a hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  exact lt_of_le_of_lt (steinF_lip z a b) hab

lemma Qm_zero_le : Qm 0 ≤ 3 := by
  unfold Qm
  have hphi : phi 0 = (√(2 * π))⁻¹ := by simp [phi]
  rw [hphi, div_inv_eq_mul]
  have h1 : √(2 * π) ≤ 3 := by
    calc √(2 * π) ≤ √(3 ^ 2) := Real.sqrt_le_sqrt (by linarith [Real.pi_lt_d2])
      _ = 3 := Real.sqrt_sq (by norm_num)
  have := mul_le_mul (Phi_le_one 0) h1 (Real.sqrt_nonneg _) (by norm_num)
  linarith

end P99bcb804

end X33_Stein

section X34_BdBE

/-! Berry–Esseen for independent, non-identically distributed, uniformly bounded summands
(Stein's method, bounded case, cf. Chen–Goldstein–Shao, Normal Approximation by Stein's Method,
§3.1): if `|ξ_i| ≤ δ ≤ 1`, `E ξ_i = 0`, `Σ E ξ_i² = 1`, then `|P(W < z) - Φ(z)| ≤ 7δ`. -/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace P99bcb804

lemma sq_bdd {a C : ℝ} (h : |a| ≤ C) : |a ^ 2| ≤ C ^ 2 := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg a) h 2

section Prob

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ι : Type} [Fintype ι] [DecidableEq ι]

lemma intB {f : Ω → ℝ} (hf : Measurable f) (C : ℝ) (h : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact h ω)

variable (ξ : ι → Ω → ℝ) (hind : iIndepFun ξ P) (hmeas : ∀ i, Measurable (ξ i)) {δ : ℝ}
  (hδ : 0 < δ) (hb : ∀ i ω, |ξ i ω| ≤ δ) (h0 : ∀ i, ∫ ω, ξ i ω ∂P = 0)
  (h1 : ∑ i, ∫ ω, ξ i ω ^ 2 ∂P = 1)
include hind hmeas hδ hb h0 h1

lemma bdd_W (ω : Ω) : |∑ i, ξ i ω| ≤ Fintype.card ι * δ := by
  calc |∑ i, ξ i ω| ≤ ∑ i, |ξ i ω| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ => hb i ω
    _ = Fintype.card ι * δ := by simp

lemma bdd_Q (ω : Ω) : |∑ i, ξ i ω ^ 2| ≤ Fintype.card ι * δ ^ 2 := by
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  calc ∑ i, ξ i ω ^ 2 ≤ ∑ _i : ι, δ ^ 2 := Finset.sum_le_sum fun i _ => by
        have := hb i ω; nlinarith [sq_abs (ξ i ω), abs_nonneg (ξ i ω)]
    _ = Fintype.card ι * δ ^ 2 := by simp

/-- Leave-one-out orthogonality `E[ξ_i g(W - ξ_i)] = 0`. -/
lemma loo_zero (g : ℝ → ℝ) (hg : Measurable g) (G : ℝ) (hG : ∀ w, |g w| ≤ G) (i : ι) :
    ∫ ω, ξ i ω * g (∑ j, ξ j ω - ξ i ω) ∂P = 0 := by
  have hind' : IndepFun (∑ j ∈ univ.erase i, ξ j) (ξ i) P :=
    hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_erase i univ)
  have hc := (hind'.comp hg measurable_id).symm
  have e : ∀ ω, ∑ j, ξ j ω - ξ i ω = (∑ j ∈ univ.erase i, ξ j) ω := by
    intro ω
    rw [Finset.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  simp_rw [e]
  have hS : Measurable (∑ j ∈ univ.erase i, ξ j) := by
    rw [show (∑ j ∈ univ.erase i, ξ j) = fun ω => ∑ j ∈ univ.erase i, ξ j ω from by
      funext ω; simp [Finset.sum_apply]]
    exact Finset.measurable_sum _ fun j _ => hmeas j
  have := hc.integral_fun_mul_eq_mul_integral (hmeas i).aestronglyMeasurable
    (hg.comp hS).aestronglyMeasurable
  simp only [Function.comp, id] at this
  rw [this, h0 i, zero_mul]

lemma moments :
    ∫ ω, (∑ i, ξ i ω ^ 2) ∂P = 1 ∧ ∫ ω, (∑ i, ξ i ω) ^ 2 ∂P = 1 ∧
      ∫ ω, (∑ i, ξ i ω ^ 2) ^ 2 ∂P ≤ 1 + δ ^ 2 ∧
      ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P ≤ δ ^ 2 := by
  have hmem : ∀ i, MemLp (ξ i) 2 P := fun i =>
    MemLp.of_bound (hmeas i).aestronglyMeasurable δ
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb i ω)
  have hsq : ∀ i, Measurable (fun ω => ξ i ω ^ 2) := fun i => (hmeas i).pow_const 2
  have hmem2 : ∀ i, MemLp (fun ω => ξ i ω ^ 2) 2 P := fun i =>
    MemLp.of_bound (hsq i).aestronglyMeasurable (δ ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rw [← sq_abs (ξ i ω)]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i ω) 2)
  have hint : ∀ i, Integrable (ξ i) P := fun i => (hmem i).integrable one_le_two
  have hint2 : ∀ i, Integrable (fun ω => ξ i ω ^ 2) P := fun i => (hmem2 i).integrable one_le_two
  have hEQ : ∫ ω, (∑ i, ξ i ω ^ 2) ∂P = 1 := by
    rw [integral_finsetSum _ fun i _ => hint2 i]; exact h1
  -- variance of W
  have hVW := IndepFun.variance_sum (μ := P) (s := univ) (fun i _ => hmem i)
    (fun i _ j _ hij => hind.indepFun hij)
  have eW : (∑ i ∈ univ, ξ i) = fun ω => ∑ i, ξ i ω := by funext ω; simp [Finset.sum_apply]
  rw [eW] at hVW
  have hmemW : MemLp (fun ω => ∑ i, ξ i ω) 2 P := by
    have := memLp_finsetSum' (s := univ) (fun i _ => hmem i)
    rwa [eW] at this
  rw [variance_eq_sub hmemW] at hVW
  have hEW : ∫ ω, ∑ i, ξ i ω ∂P = 0 := by
    rw [integral_finsetSum _ fun i _ => hint i]; simp [h0]
  have hvi : ∀ i, variance (ξ i) P = ∫ ω, ξ i ω ^ 2 ∂P := fun i => by
    rw [variance_eq_sub (hmem i)]; simp [h0 i]
  simp only [Pi.pow_apply, hEW] at hVW
  rw [Finset.sum_congr rfl fun i _ => hvi i, h1] at hVW
  have hW2 : ∫ ω, (∑ i, ξ i ω) ^ 2 ∂P = 1 := by linarith
  -- variance of Q
  have hVQ := IndepFun.variance_sum (μ := P) (s := univ) (X := fun i ω => ξ i ω ^ 2)
    (fun i _ => hmem2 i)
    (fun i _ j _ hij => (hind.indepFun hij).comp (measurable_id.pow_const 2)
      (measurable_id.pow_const 2))
  have eQ : (∑ i ∈ univ, fun ω => ξ i ω ^ 2) = fun ω => ∑ i, ξ i ω ^ 2 := by
    funext ω; simp [Finset.sum_apply]
  rw [eQ] at hVQ
  have hmemQ : MemLp (fun ω => ∑ i, ξ i ω ^ 2) 2 P := by
    have := memLp_finsetSum' (s := univ) (fun i _ => hmem2 i)
    rwa [eQ] at this
  have hVQ0 : variance (fun ω => ∑ i, ξ i ω ^ 2) P = ∫ ω, ((∑ i, ξ i ω ^ 2) - 1) ^ 2 ∂P := by
    rw [variance_eq_integral hmemQ.aestronglyMeasurable.aemeasurable]; simp only [hEQ]
  have hVQs := variance_eq_sub hmemQ
  simp only [Pi.pow_apply, hEQ] at hVQs
  have hvi2 : ∀ i, variance (fun ω => ξ i ω ^ 2) P ≤ δ ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P := fun i => by
    rw [variance_eq_sub (hmem2 i)]
    simp only [Pi.pow_apply]
    have hle : ∫ ω, (ξ i ω ^ 2) ^ 2 ∂P ≤ ∫ ω, δ ^ 2 * ξ i ω ^ 2 ∂P := by
      refine integral_mono ((hmem2 i).integrable_sq) ((hint2 i).const_mul _) fun ω => ?_
      have := hb i ω
      have h4 : ξ i ω ^ 2 ≤ δ ^ 2 := by rw [← sq_abs (ξ i ω)]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i ω) 2
      simp only
      have h5 := mul_le_mul_of_nonneg_right h4 (sq_nonneg (ξ i ω))
      first | linarith only [h5] | nlinarith [sq_nonneg (ξ i ω)]
    rw [integral_const_mul] at hle
    linarith [sq_nonneg (∫ ω, ξ i ω ^ 2 ∂P)]
  have hsumv : ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ δ ^ 2 := by
    calc ∑ i, variance (fun ω => ξ i ω ^ 2) P ≤ ∑ i, δ ^ 2 * ∫ ω, ξ i ω ^ 2 ∂P :=
          Finset.sum_le_sum fun i _ => hvi2 i
      _ = δ ^ 2 := by rw [← Finset.mul_sum, h1, mul_one]
  refine ⟨hEQ, hW2, by linarith, ?_⟩
  rw [← hVQ0, hVQ]; exact hsumv

/-- The integrability package and the leave-one-out mean of the Stein term. -/
lemma pieces (z : ℝ) (c : ℝ) :
    Integrable (fun ω => if ∑ i, ξ i ω < c then (1:ℝ) else 0) P ∧
    Integrable (fun ω => ((∑ i, ξ i ω ^ 2) - 1) ^ 2) P ∧
    Integrable (fun ω => (∑ i, ξ i ω ^ 2) ^ 2) P ∧
    Integrable (fun ω => (∑ i, ξ i ω) ^ 2) P ∧
    Integrable (fun ω => ∑ i, ξ i ω ^ 2) P ∧
    Integrable (fun ω => Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P ∧
    ∫ ω, (Phi z - ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) ∂P = Phi z := by
  have hWm : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ fun i _ => hmeas i
  have hQm : Measurable (fun ω => ∑ i, ξ i ω ^ 2) :=
    Finset.measurable_sum _ fun i _ => (hmeas i).pow_const 2
  have hW := bdd_W ξ hind hmeas hδ hb h0 h1
  have hQ := bdd_Q ξ hind hmeas hδ hb h0 h1
  have hfm := (continuous_steinF z).measurable
  have hf3 : ∀ w, |steinF z w| ≤ 3 := fun w => by
    rw [abs_of_nonneg (steinF_nonneg z w)]; exact (steinF_le z w).trans Qm_zero_le
  have hterm : ∀ i, Integrable (fun ω => ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P := fun i =>
    intB ((hmeas i).mul (hfm.comp (hWm.sub (hmeas i)))) (δ * 3) fun ω => by
      rw [abs_mul]; exact mul_le_mul (hb i ω) (hf3 _) (abs_nonneg _) hδ.le
  have hsum : Integrable (fun ω => ∑ i, ξ i ω * steinF z (∑ j, ξ j ω - ξ i ω)) P :=
    integrable_finset_sum _ fun i _ => hterm i
  refine ⟨intB (Measurable.ite (measurableSet_lt hWm measurable_const) measurable_const
      measurable_const) 1 (fun ω => by split_ifs <;> norm_num), ?_, ?_, ?_, ?_,
    (integrable_const _).sub hsum, ?_⟩
  · exact intB ((hQm.sub_const 1).pow_const 2) ((Fintype.card ι * δ ^ 2 + 1) ^ 2) fun ω => sq_bdd (by
      have h := hQ ω; have h' := abs_sub (∑ i, ξ i ω ^ 2) 1; rw [abs_one] at h'; linarith)
  · exact intB (hQm.pow_const 2) _ fun ω => sq_bdd (hQ ω)
  · exact intB (hWm.pow_const 2) _ fun ω => sq_bdd (hW ω)
  · exact intB hQm _ hQ
  · rw [integral_sub (integrable_const _) hsum, integral_finsetSum _ fun i _ => hterm i]
    simp [loo_zero ξ hind hmeas hδ hb h0 h1 (steinF z) hfm 3 hf3]

end Prob

end P99bcb804

end X34_BdBE

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

/-- `{w | Φ w ≤ t}` has standard Gaussian mass `t` for `t ∈ [0,1]`. -/
lemma gauss_Phi_le (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (gaussianReal 0 1).real {w | Phi w ≤ t} = t := by
  rcases eq_or_lt_of_le ht1 with h1 | h1
  · subst h1
    have : {w | Phi w ≤ 1} = Set.univ := Set.eq_univ_of_forall fun w => (Phi_lt_one w).le
    rw [this, probReal_univ]
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · subst h0
    have : {w | Phi w ≤ 0} = ∅ := Set.eq_empty_of_forall_notMem fun w hw =>
      absurd (Phi_pos' w) (not_lt.mpr hw)
    rw [this, measureReal_empty]
  -- intermediate value
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.mp
    ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually (gt_mem_nhds h0))
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually (lt_mem_nhds h1))
  have hab : min a b ≤ max a b := min_le_max
  have hmem : t ∈ Set.Icc (Phi (min a b)) (Phi (max a b)) :=
    ⟨(ha _ (min_le_left _ _)).le, (hb _ (le_max_right _ _)).le⟩
  obtain ⟨w0, -, hw0⟩ := intermediate_value_Icc hab continuous_Phi'.continuousOn hmem
  have : {w | Phi w ≤ t} = Set.Iic w0 := by
    ext w; simp only [Set.mem_setOf_eq, Set.mem_Iic]; rw [← hw0]; exact Phi_strictMono.le_iff_le
  rw [this, ← cdf_eq_real]; exact hw0

lemma measurable_qnt_Phi (L : Measure ℝ) [IsProbabilityMeasure L] {s : ℝ} :
    Measurable fun w => qnt L (Phi (w / s)) := by
  refine measurable_of_Iic fun x => ?_
  have : (fun w => qnt L (Phi (w / s))) ⁻¹' Set.Iic x = {w | Phi (w / s) ≤ cdf L x} := by
    ext w; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact qnt_le_iff L (Phi_pos' _) (Phi_lt_one _) x
  rw [this]
  exact measurableSet_le ((continuous_Phi'.comp (continuous_id.div_const s)).measurable)
    measurable_const

/-- Quantile transform of a standard Gaussian has law `L`. -/
lemma map_qnt_Phi (L : Measure ℝ) [IsProbabilityMeasure L] :
    (gaussianReal 0 1).map (fun w => qnt L (Phi (w / 1))) = L := by
  have hm := measurable_qnt_Phi L (s := 1)
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun w => qnt L (Phi (w / 1)))) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  refine Measure.ext_of_Iic _ _ fun x => ?_
  rw [Measure.map_apply hm measurableSet_Iic]
  have : (fun w => qnt L (Phi (w / 1))) ⁻¹' Set.Iic x = {w | Phi w ≤ cdf L x} := by
    ext w; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq, div_one]
    exact qnt_le_iff L (Phi_pos' _) (Phi_lt_one _) x
  rw [this, ← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def,
    gauss_Phi_le _ (cdf_nonneg _ _) (cdf_le_one _ _), cdf_eq_real, ofReal_measureReal]

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

lemma map_qnt_Phi' (L : Measure ℝ) [IsProbabilityMeasure L] :
    (gaussianReal 0 1).map (fun w => qnt L (Phi w)) = L := by
  simpa using map_qnt_Phi L

lemma measurable_qnt_kernel (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    Measurable fun p : ℝ × ℝ => qnt (κ p.1) (Phi p.2) := by
  refine measurable_of_Iic fun x => ?_
  have : (fun p : ℝ × ℝ => qnt (κ p.1) (Phi p.2)) ⁻¹' Set.Iic x
      = {p : ℝ × ℝ | Phi p.2 ≤ cdf (κ p.1) x} := by
    ext p; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
    exact qnt_le_iff _ (Phi_pos' _) (Phi_lt_one _) x
  rw [this]
  have hc : Measurable fun p : ℝ × ℝ => cdf (κ p.1) x := by
    have : (fun p : ℝ × ℝ => cdf (κ p.1) x) = fun p => ((κ p.1) (Set.Iic x)).toReal := by
      funext p; rw [cdf_eq_real, measureReal_def]
    rw [this]
    exact ((κ.measurable_coe measurableSet_Iic).comp measurable_fst).ennreal_toReal
  exact measurableSet_le ((continuous_Phi'.comp continuous_snd).measurable) hc

/-- Conditional quantile coupling: a fresh standard Gaussian `w` and the kernel's quantile
transform realise `μ ⊗ₘ κ` exactly. -/
lemma map_qnt_kernel (μ : Measure ℝ) [IsProbabilityMeasure μ] (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (μ.prod (gaussianReal 0 1)).map (fun p => (p.1, qnt (κ p.1) (Phi p.2))) = μ ⊗ₘ κ := by
  have hg := measurable_qnt_kernel κ
  have hF : Measurable fun p : ℝ × ℝ => (p.1, qnt (κ p.1) (Phi p.2)) := measurable_fst.prodMk hg
  ext t ht
  rw [Measure.map_apply hF ht, Measure.prod_apply (hF ht), Measure.compProd_apply ht]
  refine lintegral_congr fun a => ?_
  have hga : Measurable fun w => qnt (κ a) (Phi w) := hg.comp (measurable_const.prodMk measurable_id)
  have e : Prod.mk a ⁻¹' ((fun p : ℝ × ℝ => (p.1, qnt (κ p.1) (Phi p.2))) ⁻¹' t)
      = (fun w => qnt (κ a) (Phi w)) ⁻¹' (Prod.mk a ⁻¹' t) := by
    ext w; simp
  rw [e, ← Measure.map_apply hga (measurable_prodMk_left ht), map_qnt_Phi']

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

section Nd8

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma L2s_bd {t1 : ℝ}
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2) {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (ht : |t| ≤ t1) : 1 / 2 ≤ L2s G σ t ∧ L2s G σ t ≤ 3 := by
  have h := hV t ht
  have hs : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0.le hσ1
  have hs0 : 0 ≤ σ ^ 2 := sq_nonneg σ
  rw [L2s]
  constructor <;> linarith [h.1, h.2]

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

theorem node_κ :
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
                                                              |P99bcb804.qnt ((P99bcb804.κC G ι σ) T)
                                                                      (P99bcb804.Phi
                                                                        (u /
                                                                          (√(P99bcb804.L2s G σ (0 : ℝ)) *
                                                                            √((2 : ℝ) * ↑(Fintype.card ι))))) -
                                                                    u| ≤
                                                                C *
                                                                  ((1 : ℝ) + u ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι)) +
                                                                    T ^ (2 : ℕ) / ((2 : ℝ) * ↑(Fintype.card ι))) := EthierKurtz.kmt_smoothed_conditional_quantile_bound

end Kl3

end P99bcb804

end X47_Kl3

section X53_Pick

/-! KMT 1976 II, (4.14): the conditional quantile transform of a uniformly chosen element of a
finite set, realised by a rank-based choice driven by a single Gaussian. The chosen element is
exactly uniform and its `f`-value is the quantile transform of the law of `f`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Index of the `u`-quantile among `n` equally likely sorted values. -/
noncomputable def kIdx (n : ℕ) (u : ℝ) : ℕ := ⌈u * n⌉₊ - 1

section rank

variable {α : Type} [Fintype α]

/-- Sorting key: lexicographic in `(f a, enumeration index)`; injective. -/
noncomputable def rkey (f : α → ℝ) (a : α) : ℝ ×ₗ Fin (Fintype.card α) :=
  toLex (f a, Fintype.equivFin α a)

lemma rkey_inj (f : α → ℝ) : Function.Injective (rkey f) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  exact (Fintype.equivFin α).injective this

open Classical in
/-- Rank of `a` in the sorted order of `f`. -/
noncomputable def rk (f : α → ℝ) (a : α) : ℕ := (Finset.univ.filter (fun b => rkey f b < rkey f a)).card

lemma rk_lt_rk (f : α → ℝ) {a b : α} (h : rkey f b < rkey f a) : rk f b < rk f a := by
  classical
  unfold rk
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨b, by simp [h], by simp⟩
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.trans h

lemma rk_lt_card (f : α → ℝ) (a : α) : rk f a < Fintype.card α := by
  classical
  unfold rk
  calc _ < (Finset.univ : Finset α).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨a, Finset.mem_univ _, by simp⟩
    _ = Fintype.card α := Finset.card_univ

lemma rk_inj (f : α → ℝ) : Function.Injective (rk f) := by
  intro a b h
  by_contra hab
  have hk : rkey f a ≠ rkey f b := fun h' => hab (rkey_inj f h')
  rcases lt_or_gt_of_ne hk with h1 | h1
  · exact absurd h (rk_lt_rk f h1).ne
  · exact absurd h (rk_lt_rk f h1).ne'

/-- The rank map as an equivalence with `Fin (card α)`. -/
noncomputable def rkE (f : α → ℝ) : α ≃ Fin (Fintype.card α) :=
  Equiv.ofBijective (fun a => ⟨rk f a, rk_lt_card f a⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => rk_inj f (congrArg Fin.val h), (Fintype.card_fin _).symm⟩)

/-- Rank-based quantile choice: the element whose rank is the `u`-quantile index. -/
noncomputable def pick [Nonempty α] (f : α → ℝ) (u : ℝ) : α :=
  (rkE f).symm ⟨min (kIdx (Fintype.card α) u) (Fintype.card α - 1),
    by have := Fintype.card_pos (α := α); omega⟩

end rank

end P99bcb804

end X53_Pick

section X54_Tree

/-! KMT 1976 II, §4: the dyadic tree construction on a block of length `2^n` (P1) and the
deterministic path inequality (P5): every partial-sum error is at most `2|e_root| + 2 D`,
where `D` is the largest sum of node errors `|Ũ - Ṽ|` along a root-to-leaf path. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Dyadic index type: `Idx 0 = Unit`, `Idx (n+1) = Idx n ⊕ Idx n` (left half first). -/
@[reducible] def Idx : ℕ → Type
  | 0 => Unit
  | n + 1 => Idx n ⊕ Idx n

instance instFintypeIdx : ∀ n, Fintype (Idx n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => haveI := instFintypeIdx n; inferInstanceAs (Fintype (Idx n ⊕ Idx n))

instance instDecEqIdx : ∀ n, DecidableEq (Idx n)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | n + 1 => haveI := instDecEqIdx n; inferInstanceAs (DecidableEq (Idx n ⊕ Idx n))

instance instUniqueIdx0 : Unique (Idx 0) := inferInstanceAs (Unique Unit)

/-- Node Gaussians: one real per internal node. -/
@[reducible] def Zn : ℕ → Type
  | 0 => Unit
  | n + 1 => ℝ × Zn n × Zn n

/-- Constructor for `Zn (n+1)`. -/
@[reducible] def Zn.mk {n : ℕ} (z0 : ℝ) (zL zR : Zn n) : Zn (n + 1) := (z0, zL, zR)

/-- In-order position of a leaf. -/
def toNat : (n : ℕ) → Idx n → ℕ
  | 0, _ => 0
  | n + 1, Sum.inl i => toNat n i
  | n + 1, Sum.inr i => 2 ^ n + toNat n i

lemma toNat_lt : ∀ (n : ℕ) (i : Idx n), toNat n i < 2 ^ n
  | 0, _ => by simp [toNat]
  | n + 1, Sum.inl i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega
  | n + 1, Sum.inr i => by
      have := toNat_lt n i; simp only [toNat, pow_succ]; omega

/-- Partial sum over the first `k` leaves. -/
noncomputable def ps (n : ℕ) (f : Idx n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => toNat n i < k), f i

lemma ps_zero (n : ℕ) (f : Idx n → ℝ) : ps n f 0 = 0 := by
  simp [ps]

lemma ps_full (n : ℕ) (f : Idx n → ℝ) {k : ℕ} (hk : 2 ^ n ≤ k) : ps n f k = ∑ i, f i := by
  unfold ps
  rw [Finset.filter_true_of_mem fun i _ => lt_of_lt_of_le (toNat_lt n i) hk]

lemma ps_succ (n : ℕ) (f : Idx (n + 1) → ℝ) (k : ℕ) :
    ps (n + 1) f k = ps n (fun i => f (Sum.inl i)) k + ps n (fun i => f (Sum.inr i)) (k - 2 ^ n) := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [show (∑ a : Idx (n + 1), if toNat (n + 1) a < k then f a else 0) =
      ∑ a : Idx n ⊕ Idx n, if toNat (n + 1) a < k then f a else 0 from rfl, Fintype.sum_sum_type]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [toNat]
  congr 1
  apply propext
  omega

/-- Half-difference of a split arrangement. -/
noncomputable def hdG {ι : Type} [Fintype ι] (x : ι ⊕ ι → ℝ) (σ : Equiv.Perm (ι ⊕ ι)) : ℝ :=
  ∑ i, (x (σ (Sum.inl i)) - x (σ (Sum.inr i)))

/-- Gaussian side: the block sum `T` splits as `(T ± √(2^(n+1)) z0)/2`. -/
noncomputable def G : (n : ℕ) → ℝ → Zn n → (Idx n → ℝ)
  | 0, T, _ => fun _ => T
  | n + 1, T, (z0, zL, zR) =>
      Sum.elim (G n ((T + √((2 : ℝ) ^ (n + 1)) * z0) / 2) zL)
        (G n ((T - √((2 : ℝ) ^ (n + 1)) * z0) / 2) zR)

/-- Largest path sum of node errors `|Ũ - Ṽ|`. -/
noncomputable def D : (n : ℕ) → (Idx n → ℝ) → Zn n → ℝ
  | 0, _, _ => 0
  | n + 1, x, (z0, zL, zR) =>
      |hdG (ι := Idx n) x (pick (hdG (ι := Idx n) x) (Phi z0)) - √((2 : ℝ) ^ (n + 1)) * z0| +
        max (D n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inl i))) zL)
          (D n (fun i => x (pick (hdG (ι := Idx n) x) (Phi z0) (Sum.inr i))) zR)

end P99bcb804

end X54_Tree

section X55_Rot

/-! P2 ingredient: the 2-D rotation `(a, b) ↦ ((a+b)/√2, (a-b)/√2)` preserves the standard
Gaussian on `ℝ × ℝ`; hence the Gaussian split `T ↦ (T ± √(2^(n+1)) z)/2` of the tree `G`
turns `N(0, 2^(n+1)) ⊗ N(0,1)` into `N(0, 2^n) ⊗ N(0, 2^n)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma sqrt2_mul : √2 * √2 = (2 : ℝ) := Real.mul_self_sqrt (by norm_num)

/-- The rotation on `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def rotL : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun v := WithLp.toLp 2 ![(v 0 + v 1) / √2, (v 0 - v 1) / √2]
  map_add' v w := by
    ext i; fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i; fin_cases i <;> simp <;> ring

lemma rotL_apply0 (v : EuclideanSpace ℝ (Fin 2)) : rotL v 0 = (v 0 + v 1) / √2 := rfl
lemma rotL_apply1 (v : EuclideanSpace ℝ (Fin 2)) : rotL v 1 = (v 0 - v 1) / √2 := rfl

lemma rot_arith (a b c d : ℝ) :
    (a + b) / √2 * ((c + d) / √2) + (a - b) / √2 * ((c - d) / √2) = a * c + b * d := by
  rw [div_mul_div_comm, div_mul_div_comm, sqrt2_mul]; ring

lemma rotL_inner (x y : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (rotL x) (rotL y) = inner ℝ x y := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, rotL_apply0, rotL_apply1, RCLike.inner_apply,
    conj_trivial]
  have := rot_arith (y 0) (y 1) (x 0) (x 1)
  linarith

noncomputable def rotE : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (rotL.isometryOfInner rotL_inner).toLinearIsometryEquiv rfl

lemma rotE_apply (v : EuclideanSpace ℝ (Fin 2)) : rotE v = rotL v := rfl

/-- `ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def e2 : ℝ × ℝ ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma e2_apply0 (p : ℝ × ℝ) : e2 p 0 = p.1 := by simp [e2]
lemma e2_apply1 (p : ℝ × ℝ) : e2 p 1 = p.2 := by simp [e2]

/-- The rotation of `ℝ × ℝ`. -/
noncomputable def rot2 (p : ℝ × ℝ) : ℝ × ℝ := ((p.1 + p.2) / √2, (p.1 - p.2) / √2)

lemma measurable_rot2 : Measurable rot2 := by
  unfold rot2; fun_prop

theorem rot2_law :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map rot2 =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  set γ := gaussianReal 0 1
  have h1 : (γ.prod γ).map e2 = stdGaussian (EuclideanSpace ℝ (Fin 2)) := by
    rw [← (measurePreserving_finTwoArrow γ).map_eq,
      Measure.map_map e2.measurable MeasurableEquiv.finTwoArrow.measurable]
    convert map_pi_eq_stdGaussian (ι := Fin 2) using 2
    funext v
    ext i
    fin_cases i <;> simp [e2]
  have hc : (e2 : ℝ × ℝ → EuclideanSpace ℝ (Fin 2)) ∘ rot2 = rotE ∘ e2 := by
    funext p
    ext i
    fin_cases i <;> simp [e2_apply0, e2_apply1, rotE_apply, rotL_apply0, rotL_apply1, rot2]
  apply MeasurableEquiv.map_measurableEquiv_injective e2
  rw [Measure.map_map e2.measurable measurable_rot2, hc,
    ← Measure.map_map rotE.continuous.measurable e2.measurable, h1, stdGaussian_map rotE]

lemma gauss_scale (c : ℝ) (v : ℝ≥0) (h : c ^ 2 = v) :
    (gaussianReal 0 1).map (c * ·) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  congr 1
  ext
  simp [h]

lemma sc_arith_p (d a b : ℝ) : (√2 * d * a + √2 * d * b) / 2 = d * ((a + b) / √2) := by
  have hs : √2 ≠ 0 := by positivity
  rw [eq_comm, mul_div_assoc', div_eq_div_iff hs two_ne_zero]
  linear_combination (-(d * (a + b))) * sqrt2_mul

lemma sc_arith_m (d a b : ℝ) : (√2 * d * a - √2 * d * b) / 2 = d * ((a - b) / √2) := by
  have hs : √2 ≠ 0 := by positivity
  rw [eq_comm, mul_div_assoc', div_eq_div_iff hs two_ne_zero]
  linear_combination (-(d * (a - b))) * sqrt2_mul

/-- The Gaussian split of the tree at level `n+1`. -/
theorem split_law (n : ℕ) :
    ((gaussianReal 0 (2 ^ (n + 1))).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2) / 2,
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2) / 2)) =
      (gaussianReal 0 (2 ^ n)).prod (gaussianReal 0 (2 ^ n)) := by
  set c := √((2 : ℝ) ^ (n + 1)) with hcdef
  set d := √((2 : ℝ) ^ n) with hddef
  have hc2 : c ^ 2 = ((2 ^ (n + 1) : ℝ≥0) : ℝ) := by
    rw [hcdef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hd2 : d ^ 2 = ((2 ^ n : ℝ≥0) : ℝ) := by
    rw [hddef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hcd : c = √2 * d := by
    rw [hcdef, hddef, ← Real.sqrt_mul (by norm_num), pow_succ, mul_comm]
  set γ := gaussianReal 0 1
  have hT : gaussianReal 0 (2 ^ (n + 1)) = γ.map (c * ·) := (gauss_scale c _ hc2).symm
  have hD : gaussianReal 0 (2 ^ n) = γ.map (d * ·) := (gauss_scale d _ hd2).symm
  have hmc : Measurable (c * · : ℝ → ℝ) := measurable_const_mul c
  have hmd : Measurable (d * · : ℝ → ℝ) := measurable_const_mul d
  have hf : Measurable (fun p : ℝ × ℝ => ((p.1 + c * p.2) / 2, (p.1 - c * p.2) / 2)) := by
    fun_prop
  rw [hT, hD, ← Measure.map_id (μ := γ), Measure.map_prod_map _ _ hmc measurable_id,
    Measure.map_prod_map _ _ hmd hmd, Measure.map_id, Measure.map_map hf (hmc.prodMap measurable_id)]
  have e : (fun p : ℝ × ℝ => ((p.1 + c * p.2) / 2, (p.1 - c * p.2) / 2)) ∘
      Prod.map (c * ·) id = Prod.map (d * ·) (d * ·) ∘ rot2 := by
    funext p
    ext
    · show (c * p.1 + c * p.2) / 2 = d * ((p.1 + p.2) / √2)
      rw [hcd]; exact sc_arith_p d p.1 p.2
    · show (c * p.1 - c * p.2) / 2 = d * ((p.1 - p.2) / √2)
      rw [hcd]; exact sc_arith_m d p.1 p.2
  rw [e, ← Measure.map_map (hmd.prodMap hmd) measurable_rot2, rot2_law]

end P99bcb804

end X55_Rot

section X56_GLaw

/-! P2: the Gaussian side `G n T z` of the tree has iid `N(0,1)` leaves when `T ~ N(0, 2^n)`
and the node Gaussians are iid `N(0,1)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

instance instMeasZn : ∀ n, MeasurableSpace (Zn n)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | n + 1 => haveI := instMeasZn n; inferInstanceAs (MeasurableSpace (ℝ × Zn n × Zn n))

/-- iid standard Gaussians on the internal nodes. -/
noncomputable def γZ : (n : ℕ) → Measure (Zn n)
  | 0 => Measure.dirac ()
  | n + 1 => (gaussianReal 0 1).prod ((γZ n).prod (γZ n))

instance instProbγZ : ∀ n, IsProbabilityMeasure (γZ n)
  | 0 => inferInstanceAs (IsProbabilityMeasure (Measure.dirac ()))
  | n + 1 => haveI := instProbγZ n
      inferInstanceAs (IsProbabilityMeasure ((gaussianReal 0 1).prod ((γZ n).prod (γZ n))))

/-- `((a,b),(c,d)) ↦ ((a,c),(b,d))` is measure preserving for product measures. -/
lemma shuffle_mp {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μ1 : Measure α) (μ2 : Measure β) (μ3 : Measure γ) (μ4 : Measure δ)
    [SFinite μ1] [SFinite μ2] [SFinite μ3] [SFinite μ4] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μ1.prod μ2).prod (μ3.prod μ4)) ((μ1.prod μ3).prod (μ2.prod μ4)) := by
  have h1 := measurePreserving_prodAssoc μ1 μ2 (μ3.prod μ4)
  have h2 := (measurePreserving_prodAssoc μ2 μ3 μ4).symm
  have h3 := (MeasurePreserving.id μ1).prod (h2)
  have h4 := (MeasurePreserving.id μ1).prod
    ((Measure.measurePreserving_swap (μ := μ2) (ν := μ3)).prod (MeasurePreserving.id μ4))
  have h5 := (MeasurePreserving.id μ1).prod (measurePreserving_prodAssoc μ3 μ2 μ4)
  have h6 := (measurePreserving_prodAssoc μ1 μ3 (μ2.prod μ4)).symm
  have h := h6.comp (h5.comp (h4.comp (h3.comp h1)))
  convert h using 1
  try (funext p; rfl)

lemma measurable_G : ∀ n : ℕ, Measurable fun p : ℝ × Zn n => G n p.1 p.2
  | 0 => measurable_pi_lambda _ fun _ => measurable_fst
  | n + 1 => by
      have ih := measurable_G n
      have hL : Measurable fun p : ℝ × Zn (n + 1) =>
          G n ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2) p.2.2.1 :=
        ih.comp ((by fun_prop : Measurable fun p : ℝ × Zn (n + 1) =>
          (p.1 + √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2).prodMk (measurable_fst.comp
            (measurable_snd.comp measurable_snd)))
      have hR : Measurable fun p : ℝ × Zn (n + 1) =>
          G n ((p.1 - √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2) p.2.2.2 :=
        ih.comp ((by fun_prop : Measurable fun p : ℝ × Zn (n + 1) =>
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2.1) / 2).prodMk (measurable_snd.comp
            (measurable_snd.comp measurable_snd)))
      have := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)).symm.measurable.comp
        (hL.prodMk hR)
      exact this

lemma split_mp (n : ℕ) :
    MeasurePreserving (fun p : ℝ × ℝ => ((p.1 + √((2 : ℝ) ^ (n + 1)) * p.2) / 2,
          (p.1 - √((2 : ℝ) ^ (n + 1)) * p.2) / 2))
      ((gaussianReal 0 (2 ^ (n + 1))).prod (gaussianReal 0 1))
      ((gaussianReal 0 (2 ^ n)).prod (gaussianReal 0 (2 ^ n))) :=
  ⟨by fun_prop, split_law n⟩

/-- P2: the Gaussian side has iid standard Gaussian leaves. -/
theorem gLaw : ∀ n : ℕ, MeasurePreserving (fun p : ℝ × Zn n => G n p.1 p.2)
    ((gaussianReal 0 (2 ^ n)).prod (γZ n)) (Measure.pi fun _ : Idx n => gaussianReal 0 1)
  | 0 => by
      have h := (measurePreserving_funUnique (gaussianReal 0 1) (Idx 0)).symm
      have h2 : MeasurePreserving (fun p : ℝ × Zn 0 => p.1)
          ((gaussianReal 0 (2 ^ 0)).prod (γZ 0)) (gaussianReal 0 1) := by
        refine ⟨measurable_fst, ?_⟩
        have : IsProbabilityMeasure (γZ 0) := instProbγZ 0
        rw [Measure.map_fst_prod]; simp
      convert h.comp h2 using 1
      funext p i; rfl
  | n + 1 => by
      have ih := gLaw n
      have := instProbγZ n
      have h1 := (measurePreserving_prodAssoc (gaussianReal 0 (2 ^ (n + 1))) (gaussianReal 0 1)
        ((γZ n).prod (γZ n))).symm
      have h2 := (split_mp n).prod (MeasurePreserving.id ((γZ n).prod (γZ n)))
      have h3 := shuffle_mp (gaussianReal 0 (2 ^ n)) (gaussianReal 0 (2 ^ n)) (γZ n) (γZ n)
      have h4 := ih.prod ih
      have h5 := measurePreserving_sumPiEquivProdPi_symm
        (fun _ : Idx n ⊕ Idx n => gaussianReal 0 1)
      have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
      convert h using 1
      · funext ⟨T, z0, zL, zR⟩ i
        rcases i with i | i <;> rfl
      · rfl

end P99bcb804

end X56_GLaw

section X57_Kx1

/-! R4 / Kx1 (Q6 tree law): a generic dyadic splitting tree `Bld f` (node at level `n` splits the
total `T` into `(T ± f n T z0)/2`), its measurability, its law (`bldLaw`: if every split is
measure preserving from `μ (n+1) ⊗ N(0,1)` to `μ n ⊗ μ n` then the leaves are iid `μ 0`), and the
conditional-quantile split for the smoothed sum laws (`xSplit`, via `disint` + `map_qnt_kernel`). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

instance instNonemptyIdxKx : ∀ n, Nonempty (Idx n)
  | 0 => ⟨()⟩
  | n + 1 => haveI := instNonemptyIdxKx n; inferInstanceAs (Nonempty (Idx n ⊕ Idx n))

lemma card_Idx_pos (n : ℕ) : 0 < Fintype.card (Idx n) := Fintype.card_pos

/-- Generic dyadic splitting tree. -/
noncomputable def Bld (f : ℕ → ℝ → ℝ → ℝ) : (n : ℕ) → ℝ → Zn n → (Idx n → ℝ)
  | 0, T, _ => fun _ => T
  | n + 1, T, (z0, zL, zR) =>
      Sum.elim (Bld f n ((T + f n T z0) / 2) zL) (Bld f n ((T - f n T z0) / 2) zR)

lemma measurable_Bld (f : ℕ → ℝ → ℝ → ℝ) (hf : ∀ n, Measurable fun p : ℝ × ℝ => f n p.1 p.2) :
    ∀ n : ℕ, Measurable fun p : ℝ × Zn n => Bld f n p.1 p.2
  | 0 => measurable_pi_lambda _ fun _ => measurable_fst
  | n + 1 => by
      have ih := measurable_Bld f hf n
      have hfn : Measurable fun p : ℝ × Zn (n + 1) => f n p.1 p.2.1 :=
        (hf n).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
      have hL : Measurable fun p : ℝ × Zn (n + 1) =>
          Bld f n ((p.1 + f n p.1 p.2.1) / 2) p.2.2.1 :=
        ih.comp (((measurable_fst.add hfn).div_const 2).prodMk (measurable_fst.comp
            (measurable_snd.comp measurable_snd)))
      have hR : Measurable fun p : ℝ × Zn (n + 1) =>
          Bld f n ((p.1 - f n p.1 p.2.1) / 2) p.2.2.2 :=
        ih.comp (((measurable_fst.sub hfn).div_const 2).prodMk (measurable_snd.comp
            (measurable_snd.comp measurable_snd)))
      have := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => ℝ)).symm.measurable.comp
        (hL.prodMk hR)
      exact this

/-- Law of the generic tree: iid leaves. -/
theorem bldLaw (μ : ℕ → Measure ℝ) [hμ : ∀ n, IsProbabilityMeasure (μ n)] (f : ℕ → ℝ → ℝ → ℝ)
    (hf : ∀ n, MeasurePreserving
      (fun p : ℝ × ℝ => ((p.1 + f n p.1 p.2) / 2, (p.1 - f n p.1 p.2) / 2))
      ((μ (n + 1)).prod (gaussianReal 0 1)) ((μ n).prod (μ n))) :
    ∀ n : ℕ, MeasurePreserving (fun p : ℝ × Zn n => Bld f n p.1 p.2)
      ((μ n).prod (γZ n)) (Measure.pi fun _ : Idx n => μ 0)
  | 0 => by
      have h := (measurePreserving_funUnique (μ 0) (Idx 0)).symm
      have h2 : MeasurePreserving (fun p : ℝ × Zn 0 => p.1) ((μ 0).prod (γZ 0)) (μ 0) := by
        refine ⟨measurable_fst, ?_⟩
        have : IsProbabilityMeasure (γZ 0) := instProbγZ 0
        rw [Measure.map_fst_prod]; simp
      convert h.comp h2 using 1
      funext p i; rfl
  | n + 1 => by
      have ih := bldLaw μ f hf n
      have := instProbγZ n
      have h1 := (measurePreserving_prodAssoc (μ (n + 1)) (gaussianReal 0 1)
        ((γZ n).prod (γZ n))).symm
      have h2 := (hf n).prod (MeasurePreserving.id ((γZ n).prod (γZ n)))
      have h3 := shuffle_mp (μ n) (μ n) (γZ n) (γZ n)
      have h4 := ih.prod ih
      have h5 := measurePreserving_sumPiEquivProdPi_symm (fun _ : Idx n ⊕ Idx n => μ 0)
      have h := h5.comp (h4.comp (h3.comp (h2.comp h1)))
      convert h using 1
      · funext ⟨T, z0, zL, zR⟩ i
        rcases i with i | i <;> rfl
      · rfl

section Kx1

variable {G : Measure ℝ} [IsProbabilityMeasure G]

/-- The conditional-quantile split of the smoothed sum law is measure preserving. -/
theorem xSplit (n : ℕ) {σ : ℝ} (hσ : σ ≠ 0) :
    MeasurePreserving
      (fun p : ℝ × ℝ => ((p.1 + qnt (κC G (Idx n) σ p.1) (Phi p.2)) / 2,
        (p.1 - qnt (κC G (Idx n) σ p.1) (Phi p.2)) / 2))
      ((sL G (Idx (n + 1)) σ).prod (gaussianReal 0 1)) ((sL G (Idx n) σ).prod (sL G (Idx n) σ)) := by
  have hN := card_Idx_pos n
  haveI : Fact (σ ≠ 0) := ⟨hσ⟩
  haveI : Fact (0 < Fintype.card (Idx n)) := ⟨hN⟩
  have hq := measurable_qnt_kernel (κC G (Idx n) σ)
  set H : ℝ × ℝ → ℝ × ℝ := fun q => ((q.1 + q.2) / 2, (q.1 - q.2) / 2) with hHdef
  have hH : Measurable H := by rw [hHdef]; fun_prop
  have hP : Measurable fun p : ℝ × ℝ => (p.1, qnt (κC G (Idx n) σ p.1) (Phi p.2)) :=
    measurable_fst.prodMk hq
  have e1 : (fun p : ℝ × ℝ => ((p.1 + qnt (κC G (Idx n) σ p.1) (Phi p.2)) / 2,
        (p.1 - qnt (κC G (Idx n) σ p.1) (Phi p.2)) / 2))
      = H ∘ (fun p : ℝ × ℝ => (p.1, qnt (κC G (Idx n) σ p.1) (Phi p.2))) := rfl
  refine ⟨hH.comp hP, ?_⟩
  have eS : sL G (Idx (n + 1)) σ = sL G (Idx n ⊕ Idx n) σ := rfl
  have hHr : H ∘ rotM = id := by
    funext p
    simp only [hHdef, rotM, Function.comp_apply, id]
    ext <;> ring
  rw [e1, ← Measure.map_map hH hP, eS, map_qnt_kernel, ← disint (Idx n) hσ hN, ρC,
    Measure.map_map hH measurable_rotM, hHr, Measure.map_id]

/-- X side of the smoothed tree: split by the conditional quantile of the half-difference. -/
noncomputable def XT (G : Measure ℝ) (σ : ℝ) : (n : ℕ) → ℝ → Zn n → (Idx n → ℝ) :=
  Bld (fun n T z0 => qnt (κC G (Idx n) σ T) (Phi z0))

lemma measurable_XT {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    Measurable fun p : ℝ × Zn n => XT G σ n p.1 p.2 := by
  refine measurable_Bld _ (fun m => ?_) n
  haveI : Fact (σ ≠ 0) := ⟨hσ⟩
  haveI : Fact (0 < Fintype.card (Idx m)) := ⟨card_Idx_pos m⟩
  exact measurable_qnt_kernel (κC G (Idx m) σ)

/-- Q6: the X side has iid leaves with the one-point smoothed law. -/
theorem xLaw {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    MeasurePreserving (fun p : ℝ × Zn n => XT G σ n p.1 p.2)
      ((sL G (Idx n) σ).prod (γZ n)) (Measure.pi fun _ : Idx n => sL G (Idx 0) σ) :=
  bldLaw (fun m => sL G (Idx m) σ) _ (fun m => xSplit m hσ) n

end Kx1

end P99bcb804

end X57_Kx1

section X58_Kx2

/-! R4 / Kx2 (Q6/Q7 deterministic part): node totals of the generic tree (`sum_Bld`), the scaled
Gaussian tree as a `Bld` tree (`Bld_gauss`), and the generic KMT path inequality `pathB` for two
splitting trees driven by the same node variables. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma sum_Bld (f : ℕ → ℝ → ℝ → ℝ) : ∀ (n : ℕ) (T : ℝ) (z : Zn n), ∑ i, Bld f n T z i = T
  | 0, T, _ => by simp [Bld]
  | n + 1, T, (z0, zL, zR) => by
      show ∑ i : Idx n ⊕ Idx n, Bld f (n + 1) T (Zn.mk z0 zL zR) i = T
      rw [Fintype.sum_sum_type]
      simp only [Bld, Sum.elim_inl, Sum.elim_inr]
      rw [sum_Bld f n, sum_Bld f n]
      ring

/-- Gaussian split scaled by `c`. -/
noncomputable def gS (c : ℝ) : ℕ → ℝ → ℝ → ℝ := fun n _ z0 => c * √((2 : ℝ) ^ (n + 1)) * z0

lemma Bld_gauss {c : ℝ} (hc : c ≠ 0) :
    ∀ (n : ℕ) (T : ℝ) (z : Zn n), Bld (gS c) n T z = fun i => c * G n (T / c) z i
  | 0, T, _ => by
      funext i; simp only [Bld, G]; field_simp
  | n + 1, T, (z0, zL, zR) => by
      funext i
      rcases i with i | i
      · show Bld (gS c) n ((T + gS c n T z0) / 2) zL i = c * G n ((T / c + √((2 : ℝ) ^ (n + 1)) * z0) / 2) zL i
        rw [Bld_gauss hc n]
        congr 3
        simp only [gS]; field_simp
      · show Bld (gS c) n ((T - gS c n T z0) / 2) zR i = c * G n ((T / c - √((2 : ℝ) ^ (n + 1)) * z0) / 2) zR i
        rw [Bld_gauss hc n]
        congr 3
        simp only [gS]; field_simp

/-- Largest path sum of node discrepancies between two splitting trees. -/
noncomputable def DB (f g : ℕ → ℝ → ℝ → ℝ) : (n : ℕ) → ℝ → ℝ → Zn n → ℝ
  | 0, _, _, _ => 0
  | n + 1, T, T', (z0, zL, zR) =>
      |f n T z0 - g n T' z0| +
        max (DB f g n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL)
          (DB f g n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR)

/-- Generic KMT path inequality. -/
theorem pathB (f g : ℕ → ℝ → ℝ → ℝ) : ∀ (n : ℕ) (T T' : ℝ) (z : Zn n) (k : ℕ),
    |ps n (Bld f n T z) k - ps n (Bld g n T' z) k| ≤ 2 * |T - T'| + 2 * DB f g n T T' z
  | 0, T, T', _, k => by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp [ps_zero, DB]
      · rw [ps_full 0 _ (by rw [pow_zero]; omega), ps_full 0 _ (by rw [pow_zero]; omega)]
        simp only [Bld, DB, Fintype.sum_unique, mul_zero, add_zero]
        have := abs_nonneg (T - T')
        linarith
  | n + 1, T, T', (z0, zL, zR), k => by
      have hD : DB f g (n + 1) T T' (Zn.mk z0 zL zR) = |f n T z0 - g n T' z0| +
          max (DB f g n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL)
            (DB f g n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR) := rfl
      have hfL : (fun i => Bld f (n + 1) T (Zn.mk z0 zL zR) (Sum.inl i))
          = Bld f n ((T + f n T z0) / 2) zL := rfl
      have hfR : (fun i => Bld f (n + 1) T (Zn.mk z0 zL zR) (Sum.inr i))
          = Bld f n ((T - f n T z0) / 2) zR := rfl
      have hgL : (fun i => Bld g (n + 1) T' (Zn.mk z0 zL zR) (Sum.inl i))
          = Bld g n ((T' + g n T' z0) / 2) zL := rfl
      have hgR : (fun i => Bld g (n + 1) T' (Zn.mk z0 zL zR) (Sum.inr i))
          = Bld g n ((T' - g n T' z0) / 2) zR := rfl
      rw [ps_succ, ps_succ, hfL, hfR, hgL, hgR, hD]
      set a := f n T z0 with ha
      set b := g n T' z0 with hb
      set DL := DB f g n ((T + a) / 2) ((T' + b) / 2) zL with hDL
      set DR := DB f g n ((T - a) / 2) ((T' - b) / 2) zR with hDR
      have hmL := le_max_left DL DR
      have hmR := le_max_right DL DR
      have a1 := abs_add_le (T - T') (a - b)
      have a2 := abs_sub (T - T') (a - b)
      have hd0 : 0 ≤ |a - b| := abs_nonneg _
      have he0 : 0 ≤ |T - T'| := abs_nonneg _
      have eL : (T + a) / 2 - (T' + b) / 2 = ((T - T') + (a - b)) / 2 := by ring
      have eR : (T - a) / 2 - (T' - b) / 2 = ((T - T') - (a - b)) / 2 := by ring
      rcases le_or_gt k (2 ^ n) with hk | hk
      · rw [show k - 2 ^ n = 0 by omega, ps_zero, ps_zero, add_zero, add_zero]
        have IH := pathB f g n ((T + a) / 2) ((T' + b) / 2) zL k
        rw [eL, abs_div, abs_two] at IH
        linarith
      · rw [ps_full n _ hk.le, ps_full n _ hk.le, sum_Bld, sum_Bld]
        have IH := pathB f g n ((T - a) / 2) ((T' - b) / 2) zR (k - 2 ^ n)
        rw [eR, abs_div, abs_two] at IH
        have e1 : (T + a) / 2 + ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) -
            ((T' + b) / 2 + ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n)) =
            ((T - T') + (a - b)) / 2 +
              (ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) -
                ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n)) := by ring
        rw [e1]
        have a3 := abs_add_le (((T - T') + (a - b)) / 2)
          (ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) - ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n))
        rw [abs_div, abs_two] at a3
        linarith

end P99bcb804

end X58_Kx2

section X59_Kx3

/-! R4 / Kx3 (Q7 deterministic part): path inequality with a cutoff level `m0` (subtrees of depth
`<= m0` are bounded crudely by the sum of absolute leaf values), the on-range predicate `OnL` on
leaves, the path functional `PQ`, and `DBc_le`: on range, the cutoff discrepancy is bounded by
`C · PQ` along some root-to-leaf path. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma abs_ps_le (n : ℕ) (f : Idx n → ℝ) (k : ℕ) : |ps n f k| ≤ ∑ i, |f i| := by
  unfold ps
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => abs_nonneg (f i))

/-- Crude size of a pair of leaf vectors. -/
noncomputable def Wb (n : ℕ) (x y : Idx n → ℝ) : ℝ := ∑ i, (|x i| + |y i|)

lemma Wb_nonneg (n : ℕ) (x y : Idx n → ℝ) : 0 ≤ Wb n x y :=
  Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _)

/-- Path discrepancy with cutoff: subtrees of depth `<= m0` contribute `Wb / 2`. -/
noncomputable def DBc (f g : ℕ → ℝ → ℝ → ℝ) (m0 : ℕ) : (n : ℕ) → ℝ → ℝ → Zn n → ℝ
  | 0, _, _, _ => 0
  | n + 1, T, T', (z0, zL, zR) =>
      if n + 1 ≤ m0 then Wb (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR))
          (Bld g (n + 1) T' (Zn.mk z0 zL zR)) / 2
      else |f n T z0 - g n T' z0| +
        max (DBc f g m0 n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL)
          (DBc f g m0 n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR)

/-- Generic KMT path inequality with cutoff. -/
theorem pathBc (f g : ℕ → ℝ → ℝ → ℝ) (m0 : ℕ) : ∀ (n : ℕ) (T T' : ℝ) (z : Zn n) (k : ℕ),
    |ps n (Bld f n T z) k - ps n (Bld g n T' z) k| ≤ 2 * |T - T'| + 2 * DBc f g m0 n T T' z
  | 0, T, T', z, k => by
      have h := pathB f g 0 T T' z k
      simpa [DB, DBc] using h
  | n + 1, T, T', (z0, zL, zR), k => by
      by_cases hm : n + 1 ≤ m0
      · have hD : DBc f g m0 (n + 1) T T' (Zn.mk z0 zL zR) =
            Wb (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) (Bld g (n + 1) T' (Zn.mk z0 zL zR)) / 2 :=
          if_pos hm
        rw [hD]
        have h1 := abs_ps_le (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) k
        have h2 := abs_ps_le (n + 1) (Bld g (n + 1) T' (Zn.mk z0 zL zR)) k
        have h3 := abs_sub (ps (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) k)
          (ps (n + 1) (Bld g (n + 1) T' (Zn.mk z0 zL zR)) k)
        have hW : Wb (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) (Bld g (n + 1) T' (Zn.mk z0 zL zR))
            = (∑ i, |Bld f (n + 1) T (Zn.mk z0 zL zR) i|) +
              ∑ i, |Bld g (n + 1) T' (Zn.mk z0 zL zR) i| := by
          rw [Wb, Finset.sum_add_distrib]
        have := abs_nonneg (T - T')
        rw [hW]
        linarith
      · have hD : DBc f g m0 (n + 1) T T' (Zn.mk z0 zL zR) = |f n T z0 - g n T' z0| +
            max (DBc f g m0 n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL)
              (DBc f g m0 n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR) := if_neg hm
        have hfL : (fun i => Bld f (n + 1) T (Zn.mk z0 zL zR) (Sum.inl i))
            = Bld f n ((T + f n T z0) / 2) zL := rfl
        have hfR : (fun i => Bld f (n + 1) T (Zn.mk z0 zL zR) (Sum.inr i))
            = Bld f n ((T - f n T z0) / 2) zR := rfl
        have hgL : (fun i => Bld g (n + 1) T' (Zn.mk z0 zL zR) (Sum.inl i))
            = Bld g n ((T' + g n T' z0) / 2) zL := rfl
        have hgR : (fun i => Bld g (n + 1) T' (Zn.mk z0 zL zR) (Sum.inr i))
            = Bld g n ((T' - g n T' z0) / 2) zR := rfl
        rw [ps_succ, ps_succ, hfL, hfR, hgL, hgR, hD]
        set a := f n T z0 with ha
        set b := g n T' z0 with hb
        set DL := DBc f g m0 n ((T + a) / 2) ((T' + b) / 2) zL with hDL
        set DR := DBc f g m0 n ((T - a) / 2) ((T' - b) / 2) zR with hDR
        have hmL := le_max_left DL DR
        have hmR := le_max_right DL DR
        have a1 := abs_add_le (T - T') (a - b)
        have a2 := abs_sub (T - T') (a - b)
        have hd0 : 0 ≤ |a - b| := abs_nonneg _
        have he0 : 0 ≤ |T - T'| := abs_nonneg _
        have eL : (T + a) / 2 - (T' + b) / 2 = ((T - T') + (a - b)) / 2 := by ring
        have eR : (T - a) / 2 - (T' - b) / 2 = ((T - T') - (a - b)) / 2 := by ring
        rcases le_or_gt k (2 ^ n) with hk | hk
        · rw [show k - 2 ^ n = 0 by omega, ps_zero, ps_zero, add_zero, add_zero]
          have IH := pathBc f g m0 n ((T + a) / 2) ((T' + b) / 2) zL k
          rw [eL, abs_div, abs_two] at IH
          linarith
        · rw [ps_full n _ hk.le, ps_full n _ hk.le, sum_Bld, sum_Bld]
          have IH := pathBc f g m0 n ((T - a) / 2) ((T' - b) / 2) zR (k - 2 ^ n)
          rw [eR, abs_div, abs_two] at IH
          have e1 : (T + a) / 2 + ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) -
              ((T' + b) / 2 + ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n)) =
              ((T - T') + (a - b)) / 2 +
                (ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) -
                  ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n)) := by ring
          rw [e1]
          have a3 := abs_add_le (((T - T') + (a - b)) / 2)
            (ps n (Bld f n ((T - a) / 2) zR) (k - 2 ^ n) -
              ps n (Bld g n ((T' - b) / 2) zR) (k - 2 ^ n))
          rw [abs_div, abs_two] at a3
          linarith

/-- On-range predicate on the leaves: every node at level `>= m0` has a moderate total and a
moderate node Gaussian. -/
def OnL (m0 : ℕ) (c ε : ℝ) : (n : ℕ) → (Idx n → ℝ) → Zn n → Prop
  | 0, _, _ => True
  | n + 1, x, (z0, zL, zR) =>
      (m0 ≤ n → |∑ i, x i| ≤ c * 2 ^ (n + 1) ∧ |z0| ≤ ε * √((2 : ℝ) ^ (n + 1))) ∧
        OnL m0 c ε n (fun i => x (Sum.inl i)) zL ∧ OnL m0 c ε n (fun i => x (Sum.inr i)) zR

/-- Path functional: node terms `1 + z0² + S²/2^(n+1)` above the cutoff, crude `Wb/2` below. -/
noncomputable def PQ (m0 : ℕ) : (n : ℕ) → (Idx n → ℝ) → (Idx n → ℝ) → Zn n → Idx n → ℝ
  | 0, _, _, _, _ => 0
  | n + 1, x, y, z, i =>
      if n + 1 ≤ m0 then Wb (n + 1) x y / 2
      else (1 + z.1 ^ 2 + (∑ j, x j) ^ 2 / 2 ^ (n + 1)) +
        Sum.elim (fun i => PQ m0 n (fun j => x (Sum.inl j)) (fun j => y (Sum.inl j)) z.2.1 i)
          (fun i => PQ m0 n (fun j => x (Sum.inr j)) (fun j => y (Sum.inr j)) z.2.2 i) i

/-- On range, the cutoff discrepancy is bounded by `C · PQ` along some path. -/
theorem DBc_le (f g : ℕ → ℝ → ℝ → ℝ) (m0 : ℕ) {c ε C : ℝ} (hC : 1 ≤ C)
    (hnode : ∀ m, m0 ≤ m → ∀ S S' z0 : ℝ, |S| ≤ c * 2 ^ (m + 1) →
      |z0| ≤ ε * √((2 : ℝ) ^ (m + 1)) →
      |f m S z0 - g m S' z0| ≤ C * (1 + z0 ^ 2 + S ^ 2 / 2 ^ (m + 1))) :
    ∀ (n : ℕ) (T T' : ℝ) (z : Zn n), OnL m0 c ε n (Bld f n T z) z →
      ∃ i, DBc f g m0 n T T' z ≤ C * PQ m0 n (Bld f n T z) (Bld g n T' z) z i
  | 0, T, T', z, _ => ⟨(), by simp [DBc, PQ]⟩
  | n + 1, T, T', (z0, zL, zR), hOn => by
      by_cases hm : n + 1 ≤ m0
      · refine ⟨Classical.arbitrary _, ?_⟩
        have hD : DBc f g m0 (n + 1) T T' (Zn.mk z0 zL zR) =
            Wb (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) (Bld g (n + 1) T' (Zn.mk z0 zL zR)) / 2 :=
          if_pos hm
        have hP : ∀ i, PQ m0 (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR))
            (Bld g (n + 1) T' (Zn.mk z0 zL zR)) (Zn.mk z0 zL zR) i =
            Wb (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR)) (Bld g (n + 1) T' (Zn.mk z0 zL zR)) / 2 :=
          fun i => if_pos hm
        rw [hD, hP]
        have := div_nonneg (Wb_nonneg (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR))
          (Bld g (n + 1) T' (Zn.mk z0 zL zR))) two_pos.le
        nlinarith
      · have hmn : m0 ≤ n := by omega
        have hD : DBc f g m0 (n + 1) T T' (Zn.mk z0 zL zR) = |f n T z0 - g n T' z0| +
            max (DBc f g m0 n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL)
              (DBc f g m0 n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR) := if_neg hm
        obtain ⟨hS, hOnL, hOnR⟩ := hOn
        have hsum : ∑ i, Bld f (n + 1) T (Zn.mk z0 zL zR) i = T := sum_Bld f (n + 1) T _
        have hS' := hS hmn
        rw [hsum] at hS'
        have hnd := hnode n hmn T T' z0 hS'.1 hS'.2
        set node := 1 + z0 ^ 2 + T ^ 2 / 2 ^ (n + 1) with hnode_def
        have hP : ∀ i, PQ m0 (n + 1) (Bld f (n + 1) T (Zn.mk z0 zL zR))
            (Bld g (n + 1) T' (Zn.mk z0 zL zR)) (Zn.mk z0 zL zR) i =
            node + Sum.elim (fun i => PQ m0 n (Bld f n ((T + f n T z0) / 2) zL)
                (Bld g n ((T' + g n T' z0) / 2) zL) zL i)
              (fun i => PQ m0 n (Bld f n ((T - f n T z0) / 2) zR)
                (Bld g n ((T' - g n T' z0) / 2) zR) zR i) i := by
          intro i
          show (if n + 1 ≤ m0 then _ else _) = _
          rw [if_neg hm, hsum]
          rfl
        rcases le_total (DBc f g m0 n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR)
            (DBc f g m0 n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL) with hLR | hLR
        · obtain ⟨i, hi⟩ := DBc_le f g m0 hC hnode n ((T + f n T z0) / 2) ((T' + g n T' z0) / 2) zL
            hOnL
          refine ⟨Sum.inl i, ?_⟩
          rw [hD, hP, max_eq_left hLR]
          simp only [Sum.elim_inl]
          rw [mul_add]
          linarith
        · obtain ⟨i, hi⟩ := DBc_le f g m0 hC hnode n ((T - f n T z0) / 2) ((T' - g n T' z0) / 2) zR
            hOnR
          refine ⟨Sum.inr i, ?_⟩
          rw [hD, hP, max_eq_right hLR]
          simp only [Sum.elim_inr]
          rw [mul_add]
          linarith

end P99bcb804

end X59_Kx3

section X67_Mom

/-! P6 (part 1): exponential moments of squared sub-Gaussian sums via the Gaussian trick. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- `E exp(g²/4) = √2 ≤ 2` for a standard Gaussian. -/
lemma gauss_sq : ∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂(gaussianReal 0 1) ≤ 2 := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (by fun_prop)]
  have hfun : ∀ x : ℝ, (gaussianPDF 0 1 * fun x => ENNReal.ofReal (exp (x ^ 2 / 4))) x =
      ENNReal.ofReal ((√(2 * π))⁻¹ * exp (-(1 / 4) * x ^ 2)) := by
    intro x
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
    congr 3
    ring
  simp_rw [hfun]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, integral_gaussian]
    have h1 : (√(2 * π))⁻¹ * √(π / (1 / 4)) = √2 := by
      have e1 : √(π / (1 / 4)) = √2 * √(2 * π) := by
        rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
      rw [e1, mul_comm (√2), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [h1]
    have : √2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc ENNReal.ofReal √2 ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  · exact (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  · exact Filter.Eventually.of_forall fun x => by positivity

end P99bcb804

end X67_Mom

section X68_Mom2

/-! P6 (part 2): exponential moments of the X-side path sums `Σ_d (U_d² + W_d²)/m_d` and of the
Gaussian path sums `Σ_d z_d²`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma card_Idx : ∀ n : ℕ, Fintype.card (Idx n) = 2 ^ n
  | 0 => rfl
  | n + 1 => by
      rw [show Fintype.card (Idx (n + 1)) = Fintype.card (Idx n ⊕ Idx n) from rfl,
        Fintype.card_sum, card_Idx n]
      ring

end P99bcb804

end X68_Mom2

section X69_Mom3

/-! P6 (part 3): path sums along the dyadic tree and their exponential moments. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Gaussian path sum: `Σ z_node²` along the path to leaf `i`. -/
noncomputable def PZ : (n : ℕ) → Zn n → Idx n → ℝ
  | 0, _, _ => 0
  | n + 1, z, Sum.inl i => z.1 ^ 2 + PZ n z.2.1 i
  | n + 1, z, Sum.inr i => z.1 ^ 2 + PZ n z.2.2 i

lemma measurable_PZ : ∀ (n : ℕ) (i : Idx n), Measurable fun z : Zn n => PZ n z i
  | 0, _ => measurable_const
  | n + 1, Sum.inl i => by
      have := instMeasZn n
      exact (measurable_fst.pow_const 2).add ((measurable_PZ n i).comp
        (measurable_fst.comp measurable_snd))
  | n + 1, Sum.inr i => by
      have := instMeasZn n
      exact (measurable_fst.pow_const 2).add ((measurable_PZ n i).comp
        (measurable_snd.comp measurable_snd))

/-- Exponential moment of the Gaussian path sum. -/
theorem momZ : ∀ (n : ℕ) (i : Idx n), ∫⁻ z, ENNReal.ofReal (exp (PZ n z i / 4)) ∂(γZ n) ≤ 2 ^ n
  | 0, i => by
      have := instProbγZ 0
      simp [PZ]
  | n + 1, Sum.inl i => by
      have := instProbγZ n
      have ih := momZ n i
      show ∫⁻ z, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.1 i) / 4))
        ∂((gaussianReal 0 1).prod ((γZ n).prod (γZ n))) ≤ 2 ^ (n + 1)
      have hfun : ∀ z : ℝ × Zn n × Zn n, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.1 i) / 4)) =
          ENNReal.ofReal (exp (z.1 ^ 2 / 4)) * (ENNReal.ofReal (exp (PZ n z.2.1 i / 4)) * 1) := by
        intro z
        rw [mul_one, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, add_div]
      simp_rw [hfun]
      have hm1 : Measurable fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)) :=
        (Real.measurable_exp.comp ((measurable_PZ n i).div_const 4)).ennreal_ofReal
      rw [lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (exp (x ^ 2 / 4)))
          (g := fun p : Zn n × Zn n => ENNReal.ofReal (exp (PZ n p.1 i / 4)) * 1) (by fun_prop)
          ((hm1.comp measurable_fst).mul measurable_const).aemeasurable,
        lintegral_prod_mul (f := fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)))
          (g := fun _ : Zn n => (1 : ℝ≥0∞)) hm1.aemeasurable aemeasurable_const]
      simp only [lintegral_const, measure_univ, mul_one]
      calc (∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂gaussianReal 0 1) *
            ∫⁻ x, ENNReal.ofReal (exp (PZ n x i / 4)) ∂γZ n ≤ 2 * 2 ^ n := mul_le_mul' gauss_sq ih
        _ = 2 ^ (n + 1) := by ring
  | n + 1, Sum.inr i => by
      have := instProbγZ n
      have ih := momZ n i
      show ∫⁻ z, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.2 i) / 4))
        ∂((gaussianReal 0 1).prod ((γZ n).prod (γZ n))) ≤ 2 ^ (n + 1)
      have hfun : ∀ z : ℝ × Zn n × Zn n, ENNReal.ofReal (exp ((z.1 ^ 2 + PZ n z.2.2 i) / 4)) =
          ENNReal.ofReal (exp (z.1 ^ 2 / 4)) * (1 * ENNReal.ofReal (exp (PZ n z.2.2 i / 4))) := by
        intro z
        rw [one_mul, ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, add_div]
      simp_rw [hfun]
      have hm1 : Measurable fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4)) :=
        (Real.measurable_exp.comp ((measurable_PZ n i).div_const 4)).ennreal_ofReal
      rw [lintegral_prod_mul (f := fun x : ℝ => ENNReal.ofReal (exp (x ^ 2 / 4)))
          (g := fun p : Zn n × Zn n => 1 * ENNReal.ofReal (exp (PZ n p.2 i / 4))) (by fun_prop)
          (measurable_const.mul (hm1.comp measurable_snd)).aemeasurable,
        lintegral_prod_mul (f := fun _ : Zn n => (1 : ℝ≥0∞))
          (g := fun z : Zn n => ENNReal.ofReal (exp (PZ n z i / 4))) aemeasurable_const hm1.aemeasurable]
      simp only [lintegral_const, measure_univ, one_mul]
      calc (∫⁻ x, ENNReal.ofReal (exp (x ^ 2 / 4)) ∂gaussianReal 0 1) *
            ∫⁻ x, ENNReal.ofReal (exp (PZ n x i / 4)) ∂γZ n ≤ 2 * 2 ^ n := mul_le_mul' gauss_sq ih
        _ = 2 ^ (n + 1) := by ring

end P99bcb804

end X69_Mom3

section X71_Tail

/-! P6/P7 (part 5): `D ≤ C (n + PZ + PBX ∘ R)` along some leaf, and the exponential tail of `D`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Markov with an exponential. -/
lemma markov_exp {α : Type} [MeasurableSpace α] (μ : Measure α) {g : α → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : 0 < c) {M : ℝ≥0∞} (hM : ∫⁻ a, ENNReal.ofReal (exp (c * g a)) ∂μ ≤ M) (s : ℝ) :
    μ {a | s < g a} ≤ M * ENNReal.ofReal (exp (-(c * s))) := by
  have hsub : {a | s < g a} ⊆ {a | ENNReal.ofReal (exp (c * s)) ≤ ENNReal.ofReal (exp (c * g a))} := by
    intro a ha
    have ha' : s < g a := ha
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div ((Real.measurable_exp.comp
    (measurable_const.mul hg)).ennreal_ofReal.aemeasurable)
    (by simpa using Real.exp_pos (c * s)) ENNReal.ofReal_ne_top).trans ?_
  rw [div_eq_mul_inv, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _), ← Real.exp_neg]
  exact mul_le_mul_of_nonneg_right hM zero_le

end P99bcb804

end X71_Tail

section X74_Block

/-! P4 + P7 assembled for one dyadic block (in progress): the root bound for every block size. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma gauss_tail (s : ℝ) :
    (gaussianReal 0 1) {w : ℝ | s < w ^ 2} ≤ 2 * ENNReal.ofReal (exp (-(1 / 4 * s))) := by
  refine markov_exp (gaussianReal 0 1) (g := fun w : ℝ => w ^ 2) (by fun_prop) (by norm_num) ?_ s
  refine le_trans (le_of_eq ?_) gauss_sq
  refine lintegral_congr fun w => ?_
  congr 2; ring

lemma measurable_ps (n k : ℕ) : Measurable fun f : Idx n → ℝ => ps n f k := by
  unfold ps; exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

end P99bcb804

end X74_Block

section X75_Glue1

/-! P8 part 1: the per-block maximal deviation `Dl`, a tail-to-mgf conversion, and the block mgf. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Tail bound to exponential moment. -/
lemma mgf_of_tail {α : Type} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : Measurable g) {a C c A : ℝ} (hC : 0 < C) (hc : 0 < c) (hA : 0 ≤ A)
    (h : ∀ s : ℝ, 0 ≤ s → μ {x | a + C * s < g x} ≤ ENNReal.ofReal (A * exp (-(c * s)))) :
    ∫⁻ x, ENNReal.ofReal (exp (c / (2 * C) * g x)) ∂μ ≤
      ENNReal.ofReal (exp (c / (2 * C) * (a + C)) +
        A * exp (c / (2 * C) * (a + 2 * C)) / (1 - exp (-(c / 2)))) := by
  set l := c / (2 * C) with hl
  have hl0 : 0 < l := by positivity
  have hlC : l * C = c / 2 := by rw [hl]; field_simp
  set q := exp (-(c / 2)) with hq
  have hq0 : 0 ≤ q := (exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hS : ∀ m : ℕ, MeasurableSet {x | a + C * (m : ℝ) < g x} := fun m =>
    measurableSet_lt measurable_const hg
  have hpt : ∀ x, ENNReal.ofReal (exp (l * g x)) ≤ ENNReal.ofReal (exp (l * (a + C))) +
      ∑' m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
        Set.indicator {x | a + C * (m : ℝ) < g x} 1 x := by
    intro x
    by_cases h1 : g x ≤ a + C
    · exact le_add_right (ENNReal.ofReal_le_ofReal
        (exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 hl0.le)))
    · push Not at h1
      set m := ⌊(g x - a) / C⌋₊ with hm
      have hpos : 1 ≤ (g x - a) / C := by rw [le_div_iff₀ hC]; linarith
      have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hpos)
      have hfl : (m : ℝ) ≤ (g x - a) / C := Nat.floor_le (by linarith)
      have hlt : (g x - a) / C < m + 1 := Nat.lt_floor_add_one _
      rw [le_div_iff₀ hC] at hfl
      rw [div_lt_iff₀ hC] at hlt
      have hcast : ((m - 1 : ℕ) : ℝ) = m - 1 := by rw [Nat.cast_sub hm1]; simp
      refine le_add_left (le_trans ?_ (ENNReal.le_tsum (m - 1)))
      have hmem : x ∈ {x | a + C * ((m - 1 : ℕ) : ℝ) < g x} := by
        show a + C * ((m - 1 : ℕ) : ℝ) < g x
        rw [hcast]; linarith
      rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
      refine ENNReal.ofReal_le_ofReal (exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hl0.le))
      rw [hcast]; linarith
  have hterm : ∀ m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
      μ {x | a + C * (m : ℝ) < g x} ≤
        ENNReal.ofReal (A * exp (l * (a + 2 * C)) * q ^ m) := by
    intro m
    refine (mul_le_mul' le_rfl (h m (Nat.cast_nonneg m))).trans ?_
    rw [← ENNReal.ofReal_mul (exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [hq, ← Real.exp_nat_mul]
    have : exp (l * (a + C * ((m : ℝ) + 2))) * (A * exp (-(c * m))) =
        A * (exp (l * (a + C * ((m : ℝ) + 2))) * exp (-(c * m))) := by ring
    rw [this, ← exp_add, mul_assoc, ← exp_add]
    congr 2
    have : l * (a + C * ((m : ℝ) + 2)) = l * (a + 2 * C) + (l * C) * m := by ring
    rw [this, hlC]; ring
  have hsum : Summable fun m : ℕ => A * exp (l * (a + 2 * C)) * q ^ m :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  calc ∫⁻ x, ENNReal.ofReal (exp (l * g x)) ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (exp (l * (a + C))) +
          ∑' m : ℕ, ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) *
            Set.indicator {x | a + C * (m : ℝ) < g x} 1 x) ∂μ := lintegral_mono hpt
    _ = ENNReal.ofReal (exp (l * (a + C))) + ∑' m : ℕ,
          ENNReal.ofReal (exp (l * (a + C * ((m : ℝ) + 2)))) * μ {x | a + C * (m : ℝ) < g x} := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun m => ((measurable_one.indicator (hS m)).const_mul _).aemeasurable]
        congr 1
        refine tsum_congr fun m => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hS m)), lintegral_indicator_one (hS m)]
    _ ≤ ENNReal.ofReal (exp (l * (a + C))) +
          ∑' m : ℕ, ENNReal.ofReal (A * exp (l * (a + 2 * C)) * q ^ m) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (exp (l * (a + C)) + A * exp (l * (a + 2 * C)) / (1 - q)) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum, tsum_mul_left,
          tsum_geometric_of_lt_one hq0 hq1, ← ENNReal.ofReal_add (exp_pos _).le
            (by have : 0 < 1 - q := by linarith
                positivity)]
        rfl

end P99bcb804

end X75_Glue1

section X76_Kx4

/-! R4 / Kx4 (Q7 probabilistic estimates for the smoothed leaves `ν = sL G (Idx 0) σ`):
`lmgf_nu` (`∫⁻ e^{tx} dν = e^{Ls t}`), `lmgf_pi` (iid sums), `chern1`, `cgf_le` (`ψ(s) ≤ 2 s²`
near 0), `tail_abs` (sub-Gaussian tail of block sums on the linear range) and `mom_on`
(exponential moment of the on-range normalised square `(Σx)²/N · 1{|Σx| ≤ tb N}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

section Kx4

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma sumL_Idx0 : sumL G (Idx 0) = G := by
  unfold sumL
  have h := measurePreserving_funUnique G (Idx 0)
  have e : (fun p : Idx 0 → ℝ => ∑ i, p i) = MeasurableEquiv.funUnique (Idx 0) ℝ := by
    funext p
    simp [MeasurableEquiv.funUnique]
  rw [e]
  exact h.map_eq

lemma lmgf_gauss (v : ℝ≥0) (t : ℝ) :
    ∫⁻ y, ENNReal.ofReal (exp (t * y)) ∂(gaussianReal 0 v) = ENNReal.ofReal (exp (v * t ^ 2 / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal t)
    (ae_of_all _ fun y => (exp_pos _).le)]
  congr 1
  have h := congrFun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := v)) t
  rw [mgf] at h
  simpa using h

lemma lmgf_G (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) {t : ℝ}
    (ht : |t| ≤ a0) :
    ∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂G = ENNReal.ofReal (exp (cgf (fun x : ℝ => x) G t)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hexp t ht) (ae_of_all _ fun x => (exp_pos _).le),
    exp_cgf (hexp t ht)]
  rfl

lemma lmgf_nu (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G) (σ : ℝ) {t : ℝ}
    (ht : |t| ≤ a0) :
    ∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂(sL G (Idx 0) σ) = ENNReal.ofReal (exp (Ls G σ t)) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (exp (t * y)) := by fun_prop
  rw [sL, sumL_Idx0, Measure.conv, lintegral_map hm measurable_add]
  calc ∫⁻ a, ENNReal.ofReal (exp (t * (a.1 + a.2))) ∂(G.prod (gaussianReal 0
        ((Fintype.card (Idx 0) : ℝ) * σ ^ 2).toNNReal))
      = ∫⁻ a, ENNReal.ofReal (exp (t * a.1)) * ENNReal.ofReal (exp (t * a.2)) ∂(G.prod
          (gaussianReal 0 ((Fintype.card (Idx 0) : ℝ) * σ ^ 2).toNNReal)) :=
        lintegral_congr fun a => by rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (exp_pos _).le]
    _ = (∫⁻ x, ENNReal.ofReal (exp (t * x)) ∂G) * ∫⁻ y, ENNReal.ofReal (exp (t * y))
          ∂(gaussianReal 0 ((Fintype.card (Idx 0) : ℝ) * σ ^ 2).toNNReal) :=
        lintegral_prod_mul hm.aemeasurable hm.aemeasurable
    _ = ENNReal.ofReal (exp (Ls G σ t)) := by
      rw [lmgf_G hexp ht, lmgf_gauss, ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, Ls]
      congr 2
      have hc : (Fintype.card (Idx 0) : ℝ) = 1 := by simp
      rw [hc, one_mul, Real.coe_toNNReal _ (sq_nonneg σ)]
      ring

lemma lmgf_pi (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (ι : Type) [Fintype ι] (σ : ℝ) {t : ℝ} (ht : |t| ≤ a0) :
    ∫⁻ x, ENNReal.ofReal (exp (t * ∑ i, x i)) ∂(Measure.pi fun _ : ι => sL G (Idx 0) σ) =
      ENNReal.ofReal (exp (Fintype.card ι * Ls G σ t)) := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (exp (t * y)) := by fun_prop
  have e : (fun x : ι → ℝ => ENNReal.ofReal (exp (t * ∑ i, x i))) =
      fun x => ∏ i, ENNReal.ofReal (exp (t * x i)) := by
    funext x
    rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le)]
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → ℝ) => ENNReal.ofReal (exp (t * x i)))
    (iIndepFun_pi (μ := fun _ : ι => sL G (Idx 0) σ) (X := fun _ => fun y => ENNReal.ofReal (exp (t * y)))
      (fun _ => hm.aemeasurable))
    (fun i => hm.comp (measurable_pi_apply i))]
  have e2 : ∀ i : ι, ∫⁻ x, ENNReal.ofReal (exp (t * x i)) ∂(Measure.pi fun _ : ι => sL G (Idx 0) σ)
      = ENNReal.ofReal (exp (Ls G σ t)) := by
    intro i
    rw [(measurePreserving_eval (fun _ : ι => sL G (Idx 0) σ) i).lintegral_comp hm, lmgf_nu hexp σ ht]
  simp_rw [e2]
  rw [Finset.prod_const, Finset.card_univ, ← ENNReal.ofReal_pow (exp_pos _).le, ← Real.exp_nat_mul]

lemma chern1 (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (ι : Type) [Fintype ι] (σ : ℝ) {t : ℝ} (ht : |t| ≤ a0) (s : ℝ) :
    (Measure.pi fun _ : ι => sL G (Idx 0) σ) {x | s < t * ∑ i, x i} ≤
      ENNReal.ofReal (exp (Fintype.card ι * Ls G σ t)) * ENNReal.ofReal (exp (-s)) := by
  have hg : Measurable fun x : ι → ℝ => t * ∑ i, x i := by fun_prop
  have h := markov_exp (Measure.pi fun _ : ι => sL G (Idx 0) σ) hg one_pos
    (M := ENNReal.ofReal (exp (Fintype.card ι * Ls G σ t)))
    (by simp_rw [one_mul]; rw [lmgf_pi hexp ι σ ht]) s
  simpa using h

lemma cgf_le (ha0 : 0 < a0) (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {s : ℝ} (hs1 : |s| ≤ t1) (hsB : B * |s| ≤ 1) : cgf (fun x : ℝ => x) G s ≤ 2 * s ^ 2 := by
  obtain ⟨-, -, h3⟩ := cum_taylor ht1 h2 hexp hW (t := 0) (s := s) (by simpa using ht1.le) hs1
  have hc0 : cgf (fun x : ℝ => x) G 0 = 0 := cgf_zero
  have hd0 : iteratedDeriv 1 (cgf (fun x : ℝ => x) G) 0 = 0 := by
    rw [iteratedDeriv_one]; exact tmu_zero ha0 hexp hm
  have hV0 := (hV 0 (by simp [ht1.le])).2
  rw [hc0, hd0, sub_zero, sub_zero, zero_mul, sub_zero] at h3
  have habs := (abs_le.1 h3).2
  have hs3 : |s| ^ 3 = |s| * s ^ 2 := by rw [pow_succ', sq_abs]
  rw [hs3] at habs
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hq : B * (|s| * s ^ 2) ≤ s ^ 2 := by rw [← mul_assoc]; exact mul_le_of_le_one_left hs2 hsB
  nlinarith

/-- Sub-Gaussian tail of block sums of smoothed leaves on the linear range. -/
theorem tail_abs (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (ι : Type) [Fintype ι] (hN : 0 < Fintype.card ι) {σ : ℝ} (hσ1 : |σ| ≤ 1) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y ≤ 6 * min t1 (1 / (B + 1)) * Fintype.card ι) :
    (Measure.pi fun _ : ι => sL G (Idx 0) σ) {x | y < |∑ i, x i|} ≤
      2 * ENNReal.ofReal (exp (-(y ^ 2 / (12 * Fintype.card ι)))) := by
  set N : ℝ := (Fintype.card ι : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by rw [hNdef]; exact_mod_cast hN
  set P := Measure.pi fun _ : ι => sL G (Idx 0) σ with hP
  rcases hy0.eq_or_lt with hy0' | hypos
  · subst hy0'
    have : P {x | (0 : ℝ) < |∑ i, x i|} ≤ 1 := prob_le_one
    refine this.trans ?_
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      exp_zero, ENNReal.ofReal_one, mul_one]
    norm_num
  set t := y / (6 * N) with htdef
  have ht0 : 0 < t := by positivity
  have htb : t ≤ min t1 (1 / (B + 1)) := by
    rw [htdef, div_le_iff₀ (by positivity)]; linarith
  have ht1' : t ≤ t1 := htb.trans (min_le_left _ _)
  have htB : B * t ≤ 1 := by
    have h := htb.trans (min_le_right _ _)
    have hB1 : 0 < B + 1 := by linarith
    rw [le_div_iff₀ hB1] at h
    linarith
  have hta : t ≤ a0 := by linarith
  have hσ2 : σ ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg σ) hσ1
  -- exponent bound for ±t
  have hexpo : ∀ u : ℝ, |u| = t → N * Ls G σ u - t * y ≤ -(y ^ 2 / (12 * N)) := by
    intro u hu
    have hc := cgf_le ha0 hexp hm ht1 h2 hV hW (s := u) (by rw [hu]; exact ht1')
      (by rw [hu]; exact htB)
    have hu2 : u ^ 2 = t ^ 2 := by rw [← sq_abs, hu]
    have hL : Ls G σ u ≤ 3 * t ^ 2 := by
      rw [Ls, ← hu2]
      have : u ^ 2 * σ ^ 2 ≤ u ^ 2 := mul_le_of_le_one_right (sq_nonneg u) hσ2
      have := sq_nonneg u
      linarith
    have e : N * (3 * t ^ 2) - t * y = -(y ^ 2 / (12 * N)) := by
      rw [htdef]; field_simp; ring
    have := mul_le_mul_of_nonneg_left hL hN0.le
    linarith
  have hup : P {x | y < ∑ i, x i} ≤ ENNReal.ofReal (exp (-(y ^ 2 / (12 * N)))) := by
    have hsub : {x : ι → ℝ | y < ∑ i, x i} ⊆ {x | t * y < t * ∑ i, x i} := fun x hx =>
      mul_lt_mul_of_pos_left hx ht0
    refine (measure_mono hsub).trans ((chern1 hexp ι σ (by rw [abs_of_pos ht0]; exact hta)
      (t * y)).trans ?_)
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      have := hexpo t (abs_of_pos ht0); linarith))
  have hlo : P {x | y < -∑ i, x i} ≤ ENNReal.ofReal (exp (-(y ^ 2 / (12 * N)))) := by
    have hsub : {x : ι → ℝ | y < -∑ i, x i} ⊆ {x | t * y < (-t) * ∑ i, x i} := fun x hx => by
      have := mul_lt_mul_of_pos_left hx ht0
      show t * y < (-t) * ∑ i, x i; linarith
    refine (measure_mono hsub).trans ((chern1 hexp ι σ (by rw [abs_neg, abs_of_pos ht0]; exact hta)
      (t * y)).trans ?_)
    rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by
      have := hexpo (-t) (by rw [abs_neg, abs_of_pos ht0]); linarith))
  have hsub : {x : ι → ℝ | y < |∑ i, x i|} ⊆ {x | y < ∑ i, x i} ∪ {x | y < -∑ i, x i} := by
    intro x hx
    rcases lt_abs.1 (show y < |∑ i, x i| from hx) with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [two_mul]
  exact add_le_add hup hlo

end Kx4

end P99bcb804

end X76_Kx4

section X77_Kx5

/-! R4 / Kx5 (Q7 path moments): leaf-side on-range predicate `OnX`, Gaussian-side `OnZ`
(`OnL_of`), the X path functional `PX` (normalised squared block sums above the cutoff), the
crude cutoff-block size `Wx`, the decomposition `PQ_le` (`PQ ≤ n + PZ + PX + (Wx x + Wx y)/2`),
and the moment recursion `momPX` on the on-range event (generic leaf law `F`). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Leaf-side on-range predicate. -/
def OnX (m0 : ℕ) (c : ℝ) : (n : ℕ) → (Idx n → ℝ) → Prop
  | 0, _ => True
  | n + 1, x => (m0 ≤ n → |∑ i, x i| ≤ c * 2 ^ (n + 1)) ∧
      OnX m0 c n (fun i => x (Sum.inl i)) ∧ OnX m0 c n (fun i => x (Sum.inr i))

/-- Gaussian-side on-range predicate. -/
def OnZ (m0 : ℕ) (ε : ℝ) : (n : ℕ) → Zn n → Prop
  | 0, _ => True
  | n + 1, z => (m0 ≤ n → |z.1| ≤ ε * √((2 : ℝ) ^ (n + 1))) ∧ OnZ m0 ε n z.2.1 ∧ OnZ m0 ε n z.2.2

lemma OnL_of (m0 : ℕ) (c ε : ℝ) : ∀ (n : ℕ) (x : Idx n → ℝ) (z : Zn n),
    OnX m0 c n x → OnZ m0 ε n z → OnL m0 c ε n x z
  | 0, _, _, _, _ => trivial
  | n + 1, x, (z0, zL, zR), hx, hz => by
      obtain ⟨hx1, hxL, hxR⟩ := hx
      obtain ⟨hz1, hzL, hzR⟩ := hz
      exact ⟨fun h => ⟨hx1 h, hz1 h⟩, OnL_of m0 c ε n _ zL hxL hzL, OnL_of m0 c ε n _ zR hxR hzR⟩

lemma OnX_top {m0 : ℕ} {c : ℝ} {d : ℕ} (hd : m0 < d) {x : Idx d → ℝ} (h : OnX m0 c d x) :
    |∑ i, x i| ≤ c * 2 ^ d := by
  cases d with
  | zero => omega
  | succ d => exact h.1 (by omega)

lemma measurableSet_OnX (m0 : ℕ) (c : ℝ) :
    ∀ d : ℕ, MeasurableSet {x : Idx d → ℝ | OnX m0 c d x}
  | 0 => by
      have : {x : Idx 0 → ℝ | OnX m0 c 0 x} = Set.univ := by ext x; simp [OnX]
      rw [this]; exact MeasurableSet.univ
  | d + 1 => by
      have hL : Measurable fun x : Idx (d + 1) → ℝ => fun j : Idx d => x (Sum.inl j) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply _
      have hR : Measurable fun x : Idx (d + 1) → ℝ => fun j : Idx d => x (Sum.inr j) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply _
      have htop : MeasurableSet {x : Idx (d + 1) → ℝ | m0 ≤ d → |∑ i, x i| ≤ c * 2 ^ (d + 1)} := by
        by_cases h : m0 ≤ d
        · simp only [h, true_implies]
          exact measurableSet_le (by fun_prop) measurable_const
        · simp only [h, false_implies, Set.setOf_true]
          exact MeasurableSet.univ
      have e : {x : Idx (d + 1) → ℝ | OnX m0 c (d + 1) x} =
          {x : Idx (d + 1) → ℝ | m0 ≤ d → |∑ i, x i| ≤ c * 2 ^ (d + 1)} ∩
            ((fun x : Idx (d + 1) → ℝ => fun j : Idx d => x (Sum.inl j)) ⁻¹'
              {x : Idx d → ℝ | OnX m0 c d x} ∩
            (fun x : Idx (d + 1) → ℝ => fun j : Idx d => x (Sum.inr j)) ⁻¹'
              {x : Idx d → ℝ | OnX m0 c d x}) := by
        ext x; rfl
      rw [e]
      exact htop.inter ((hL (measurableSet_OnX m0 c d)).inter (hR (measurableSet_OnX m0 c d)))

/-- X path functional: normalised squared block sums of depth `> m0` along the path. -/
noncomputable def PX (m0 : ℕ) : (n : ℕ) → (Idx n → ℝ) → Idx n → ℝ
  | 0, _, _ => 0
  | n + 1, x, Sum.inl i =>
      (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0) + PX m0 n (fun j => x (Sum.inl j)) i
  | n + 1, x, Sum.inr i =>
      (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0) + PX m0 n (fun j => x (Sum.inr j)) i

lemma top_nonneg (m0 n : ℕ) (x : Idx (n + 1) → ℝ) :
    0 ≤ (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0) := by
  split_ifs
  · positivity
  · exact le_refl _

lemma PX_nonneg (m0 : ℕ) : ∀ (n : ℕ) (x : Idx n → ℝ) (i : Idx n), 0 ≤ PX m0 n x i
  | 0, _, _ => le_refl _
  | n + 1, x, Sum.inl i => add_nonneg (top_nonneg m0 n x) (PX_nonneg m0 n _ i)
  | n + 1, x, Sum.inr i => add_nonneg (top_nonneg m0 n x) (PX_nonneg m0 n _ i)

lemma PX_eq_zero (m0 : ℕ) : ∀ (n : ℕ), n ≤ m0 → ∀ (x : Idx n → ℝ) (i : Idx n), PX m0 n x i = 0
  | 0, _, _, _ => rfl
  | n + 1, hn, x, Sum.inl i => by
      show (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0) + PX m0 n _ i = 0
      rw [if_neg (by omega), PX_eq_zero m0 n (by omega), add_zero]
  | n + 1, hn, x, Sum.inr i => by
      show (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0) + PX m0 n _ i = 0
      rw [if_neg (by omega), PX_eq_zero m0 n (by omega), add_zero]

lemma measurable_PX (m0 : ℕ) : ∀ (n : ℕ) (i : Idx n), Measurable fun x : Idx n → ℝ => PX m0 n x i
  | 0, _ => measurable_const
  | n + 1, Sum.inl i => by
      have hL : Measurable fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inl j) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply _
      have ht : Measurable fun x : Idx (n + 1) → ℝ =>
          (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0 : ℝ) := by
        by_cases h : m0 ≤ n
        · simp only [h, if_true]; fun_prop
        · simp only [h, if_false]; exact measurable_const
      exact ht.add ((measurable_PX m0 n i).comp hL)
  | n + 1, Sum.inr i => by
      have hR : Measurable fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inr j) :=
        measurable_pi_lambda _ fun j => measurable_pi_apply _
      have ht : Measurable fun x : Idx (n + 1) → ℝ =>
          (if m0 ≤ n then (∑ j, x j) ^ 2 / 2 ^ (n + 1) else 0 : ℝ) := by
        by_cases h : m0 ≤ n
        · simp only [h, if_true]; fun_prop
        · simp only [h, if_false]; exact measurable_const
      exact ht.add ((measurable_PX m0 n i).comp hR)

/-- Crude size `Σ |x|` of the cutoff block containing leaf `i`. -/
noncomputable def Wx (m0 : ℕ) : (n : ℕ) → (Idx n → ℝ) → Idx n → ℝ
  | 0, x, _ => ∑ j, |x j|
  | n + 1, x, i =>
      if n + 1 ≤ m0 then ∑ j, |x j|
      else Sum.elim (fun i => Wx m0 n (fun j => x (Sum.inl j)) i)
        (fun i => Wx m0 n (fun j => x (Sum.inr j)) i) i

lemma Wx_nonneg (m0 : ℕ) : ∀ (n : ℕ) (x : Idx n → ℝ) (i : Idx n), 0 ≤ Wx m0 n x i
  | 0, x, _ => Finset.sum_nonneg fun j _ => abs_nonneg (x j)
  | n + 1, x, i => by
      show 0 ≤ (if n + 1 ≤ m0 then ∑ j, |x j| else Sum.elim (fun i => Wx m0 n (fun j => x (Sum.inl j)) i)
        (fun i => Wx m0 n (fun j => x (Sum.inr j)) i) i)
      split_ifs
      · exact Finset.sum_nonneg fun j _ => abs_nonneg (x j)
      · rcases i with i | i
        · exact Wx_nonneg m0 n _ i
        · exact Wx_nonneg m0 n _ i

lemma PZ_nonneg' : ∀ (n : ℕ) (z : Zn n) (i : Idx n), 0 ≤ PZ n z i
  | 0, _, _ => le_refl _
  | n + 1, z, Sum.inl i => add_nonneg (sq_nonneg _) (PZ_nonneg' n _ i)
  | n + 1, z, Sum.inr i => add_nonneg (sq_nonneg _) (PZ_nonneg' n _ i)

/-- Decomposition of the path functional. -/
theorem PQ_le (m0 : ℕ) : ∀ (n : ℕ) (x y : Idx n → ℝ) (z : Zn n) (i : Idx n),
    PQ m0 n x y z i ≤ n + PZ n z i + PX m0 n x i + (Wx m0 n x i + Wx m0 n y i) / 2
  | 0, x, y, z, i => by
      have := Wx_nonneg m0 0 x i; have := Wx_nonneg m0 0 y i
      simp only [PQ, PZ, PX, CharP.cast_eq_zero]
      linarith
  | n + 1, x, y, (z0, zL, zR), i => by
      have hP0 := PZ_nonneg' (n + 1) (Zn.mk z0 zL zR) i
      have hX0 := PX_nonneg m0 (n + 1) x i
      by_cases hm : n + 1 ≤ m0
      · have e1 : PQ m0 (n + 1) x y (Zn.mk z0 zL zR) i = Wb (n + 1) x y / 2 := if_pos hm
        have e2 : Wx m0 (n + 1) x i = ∑ j, |x j| := if_pos hm
        have e3 : Wx m0 (n + 1) y i = ∑ j, |y j| := if_pos hm
        rw [e1, e2, e3, Wb, Finset.sum_add_distrib]
        have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      · have hmn : m0 ≤ n := by omega
        have hW : ∀ v : Idx (n + 1) → ℝ, Wx m0 (n + 1) v i =
            Sum.elim (fun i => Wx m0 n (fun j => v (Sum.inl j)) i)
              (fun i => Wx m0 n (fun j => v (Sum.inr j)) i) i := fun v => if_neg hm
        have e1 : PQ m0 (n + 1) x y (Zn.mk z0 zL zR) i =
            (1 + z0 ^ 2 + (∑ j, x j) ^ 2 / 2 ^ (n + 1)) +
            Sum.elim (fun i => PQ m0 n (fun j => x (Sum.inl j)) (fun j => y (Sum.inl j)) zL i)
              (fun i => PQ m0 n (fun j => x (Sum.inr j)) (fun j => y (Sum.inr j)) zR i) i := if_neg hm
        rw [e1, hW x, hW y]
        push_cast
        rcases i with i | i
        · have IH := PQ_le m0 n (fun j => x (Sum.inl j)) (fun j => y (Sum.inl j)) zL i
          have hPZ : PZ (n + 1) (Zn.mk z0 zL zR) (Sum.inl i) = z0 ^ 2 + PZ n zL i := rfl
          have hPX : PX m0 (n + 1) x (Sum.inl i) = (∑ j, x j) ^ 2 / 2 ^ (n + 1) +
              PX m0 n (fun j => x (Sum.inl j)) i := by
            show (if m0 ≤ n then _ else _) + _ = _; rw [if_pos hmn]
          simp only [Sum.elim_inl]
          rw [hPZ, hPX]
          linarith
        · have IH := PQ_le m0 n (fun j => x (Sum.inr j)) (fun j => y (Sum.inr j)) zR i
          have hPZ : PZ (n + 1) (Zn.mk z0 zL zR) (Sum.inr i) = z0 ^ 2 + PZ n zR i := rfl
          have hPX : PX m0 (n + 1) x (Sum.inr i) = (∑ j, x j) ^ 2 / 2 ^ (n + 1) +
              PX m0 n (fun j => x (Sum.inr j)) i := by
            show (if m0 ≤ n then _ else _) + _ = _; rw [if_pos hmn]
          simp only [Sum.elim_inr]
          rw [hPZ, hPX]
          linarith

lemma split_int (F : Measure ℝ) [IsProbabilityMeasure F] (d : ℕ) {u v : (Idx d → ℝ) → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) :
    ∫⁻ x, u (fun j => x (Sum.inl j)) * v (fun j => x (Sum.inr j))
        ∂(Measure.pi fun _ : Idx (d + 1) => F) =
      (∫⁻ x, u x ∂(Measure.pi fun _ : Idx d => F)) * ∫⁻ x, v x ∂(Measure.pi fun _ : Idx d => F) := by
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : Idx d ⊕ Idx d => F)
  have e := hmp.lintegral_comp_emb
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Idx d ⊕ Idx d => ℝ)).measurableEmbedding
    (fun p : (Idx d → ℝ) × (Idx d → ℝ) => u p.1 * v p.2)
  rw [← lintegral_prod_mul hu.aemeasurable hv.aemeasurable]
  exact e

/-- Truncated normalised square of the block sum. -/
noncomputable def trq (c : ℝ) (d : ℕ) (x : Idx d → ℝ) : ℝ :=
  if |∑ i, x i| ≤ c * 2 ^ d then (∑ i, x i) ^ 2 / 2 ^ d else 0

/-- Top term above the cutoff. -/
noncomputable def tpq (m0 : ℕ) (d : ℕ) (x : Idx d → ℝ) : ℝ :=
  if m0 < d then (∑ i, x i) ^ 2 / 2 ^ d else 0

lemma measurable_trq (c : ℝ) (d : ℕ) : Measurable (trq c d) := by
  unfold trq
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop)
    measurable_const

lemma measurable_tpq (m0 d : ℕ) : Measurable (tpq m0 d) := by
  unfold tpq
  by_cases h : m0 < d
  · simp only [h, if_true]; fun_prop
  · simp only [h, if_false]; exact measurable_const

lemma sq_split1 {SL SR P2 : ℝ} (hP : 0 < P2) :
    4 * ((SL + SR) ^ 2 / (2 * P2)) ≤ 3 * (SL ^ 2 / P2) + 6 * (SR ^ 2 / P2) := by
  have e1 : 4 * ((SL + SR) ^ 2 / (2 * P2)) = 2 * (SL + SR) ^ 2 / P2 := by field_simp; ring
  have e2 : 3 * (SL ^ 2 / P2) + 6 * (SR ^ 2 / P2) = (3 * SL ^ 2 + 6 * SR ^ 2) / P2 := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by linarith [sq_nonneg (SL - 2 * SR)]) hP.le

lemma sq_split2 {SL SR P2 : ℝ} (hP : 0 < P2) :
    4 * ((SL + SR) ^ 2 / (2 * P2)) ≤ 6 * (SL ^ 2 / P2) + 3 * (SR ^ 2 / P2) := by
  have e1 : 4 * ((SL + SR) ^ 2 / (2 * P2)) = 2 * (SL + SR) ^ 2 / P2 := by field_simp; ring
  have e2 : 6 * (SL ^ 2 / P2) + 3 * (SR ^ 2 / P2) = (6 * SL ^ 2 + 3 * SR ^ 2) / P2 := by ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (by linarith [sq_nonneg (2 * SL - SR)]) hP.le

/-- Moment recursion for the X path functional on the on-range event. -/
theorem momPX (F : Measure ℝ) [IsProbabilityMeasure F] (m0 : ℕ) {c l A1 : ℝ} (hl : 0 ≤ l)
    (hA1 : 1 ≤ A1)
    (hmom : ∀ d : ℕ, ∫⁻ x, ENNReal.ofReal (exp (6 * l * trq c d x))
      ∂(Measure.pi fun _ : Idx d => F) ≤ ENNReal.ofReal A1) :
    ∀ (d : ℕ) (i : Idx d), ∫⁻ x, {x | OnX m0 c d x}.indicator
      (fun x => ENNReal.ofReal (exp (l * PX m0 d x i + 3 * l * tpq m0 d x))) x
        ∂(Measure.pi fun _ : Idx d => F) ≤ ENNReal.ofReal (A1 ^ d) := by
  have hA0 : 0 ≤ A1 := by linarith
  have hVm : ∀ d, Measurable fun x : Idx d → ℝ => ENNReal.ofReal (exp (6 * l * trq c d x)) :=
    fun d => (Real.measurable_exp.comp (measurable_const.mul (measurable_trq c d))).ennreal_ofReal
  have hUm : ∀ d (i : Idx d), Measurable fun x : Idx d → ℝ => {x | OnX m0 c d x}.indicator
      (fun x => ENNReal.ofReal (exp (l * PX m0 d x i + 3 * l * tpq m0 d x))) x := fun d i =>
    ((Real.measurable_exp.comp ((measurable_const.mul (measurable_PX m0 d i)).add
      (measurable_const.mul (measurable_tpq m0 d)))).ennreal_ofReal).indicator
      (measurableSet_OnX m0 c d)
  have hle1 : ∀ d (i : Idx d) (x : Idx d → ℝ), PX m0 d x i = 0 → tpq m0 d x = 0 →
      {x | OnX m0 c d x}.indicator
        (fun x => ENNReal.ofReal (exp (l * PX m0 d x i + 3 * l * tpq m0 d x))) x ≤ 1 := by
    intro d i x h1 h2
    refine (Set.indicator_le_self _ _ x).trans ?_
    simp [h1, h2]
  intro d
  induction d with
  | zero =>
    intro i
    calc _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂(Measure.pi fun _ : Idx 0 => F) :=
          lintegral_mono fun x => hle1 0 i x rfl (by simp [tpq])
      _ = ENNReal.ofReal (A1 ^ 0) := by simp
  | succ d ih =>
    intro i
    rcases lt_trichotomy m0 d with h | h | h
    · -- m0 < d: split into the two halves
      have hP : (0 : ℝ) < 2 ^ d := by positivity
      have h2 : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
      have key : ∀ (x : Idx (d + 1) → ℝ) (j : Idx d) (hj : i = Sum.inl j ∨ i = Sum.inr j),
          {x | OnX m0 c (d + 1) x}.indicator
            (fun x => ENNReal.ofReal (exp (l * PX m0 (d + 1) x i + 3 * l * tpq m0 (d + 1) x))) x ≤
          (if i = Sum.inl j then
            {x | OnX m0 c d x}.indicator (fun x => ENNReal.ofReal
              (exp (l * PX m0 d x j + 3 * l * tpq m0 d x))) (fun k => x (Sum.inl k)) *
              ENNReal.ofReal (exp (6 * l * trq c d (fun k => x (Sum.inr k))))
          else
            ENNReal.ofReal (exp (6 * l * trq c d (fun k => x (Sum.inl k)))) *
            {x | OnX m0 c d x}.indicator (fun x => ENNReal.ofReal
              (exp (l * PX m0 d x j + 3 * l * tpq m0 d x))) (fun k => x (Sum.inr k))) := by
        intro x j hj
        by_cases hx : OnX m0 c (d + 1) x
        · have hx' := hx
          obtain ⟨-, hxL, hxR⟩ := hx'
          rw [Set.indicator_of_mem (show x ∈ {x | OnX m0 c (d + 1) x} from hx)]
          have hSL := OnX_top h hxL
          have hSR := OnX_top h hxR
          set SL := ∑ k, x (Sum.inl k) with hSLd
          set SR := ∑ k, x (Sum.inr k) with hSRd
          have hS : ∑ k, x k = SL + SR := Fintype.sum_sum_type (fun k : Idx d ⊕ Idx d => x k)
          have htp1 : tpq m0 (d + 1) x = (SL + SR) ^ 2 / (2 * 2 ^ d) := by
            rw [tpq, if_pos (by omega), hS, h2]
          have htpL : tpq m0 d (fun k => x (Sum.inl k)) = SL ^ 2 / 2 ^ d := by rw [tpq, if_pos h]
          have htpR : tpq m0 d (fun k => x (Sum.inr k)) = SR ^ 2 / 2 ^ d := by rw [tpq, if_pos h]
          have htrL : trq c d (fun k => x (Sum.inl k)) = SL ^ 2 / 2 ^ d := by rw [trq, if_pos hSL]
          have htrR : trq c d (fun k => x (Sum.inr k)) = SR ^ 2 / 2 ^ d := by rw [trq, if_pos hSR]
          rcases hj with rfl | rfl
          · rw [if_pos rfl, Set.indicator_of_mem (show (fun k => x (Sum.inl k)) ∈
              {x | OnX m0 c d x} from hxL), ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
            apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.2
            have hPX : PX m0 (d + 1) x (Sum.inl j) = (SL + SR) ^ 2 / (2 * 2 ^ d) +
                PX m0 d (fun k => x (Sum.inl k)) j := by
              show (if m0 ≤ d then _ else _) + _ = _
              rw [if_pos h.le, hS, h2]
            rw [hPX, htp1, htpL, htrR]
            have := mul_le_mul_of_nonneg_left (sq_split1 (SL := SL) (SR := SR) hP) hl
            linarith
          · rw [if_neg (by simp), Set.indicator_of_mem (show (fun k => x (Sum.inr k)) ∈
              {x | OnX m0 c d x} from hxR), ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
            apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.2
            have hPX : PX m0 (d + 1) x (Sum.inr j) = (SL + SR) ^ 2 / (2 * 2 ^ d) +
                PX m0 d (fun k => x (Sum.inr k)) j := by
              show (if m0 ≤ d then _ else _) + _ = _
              rw [if_pos h.le, hS, h2]
            rw [hPX, htp1, htpR, htrL]
            have := mul_le_mul_of_nonneg_left (sq_split2 (SL := SL) (SR := SR) hP) hl
            linarith
        · rw [Set.indicator_of_notMem (show x ∉ {x | OnX m0 c (d + 1) x} from hx)]
          exact bot_le
      rcases i with j | j
      · calc _ ≤ ∫⁻ x, {x | OnX m0 c d x}.indicator (fun x => ENNReal.ofReal
                (exp (l * PX m0 d x j + 3 * l * tpq m0 d x))) (fun k => x (Sum.inl k)) *
                ENNReal.ofReal (exp (6 * l * trq c d (fun k => x (Sum.inr k))))
                ∂(Measure.pi fun _ : Idx (d + 1) => F) :=
              lintegral_mono fun x => by
                have := key x j (Or.inl rfl); rwa [if_pos rfl] at this
          _ = _ := split_int F d (hUm d j) (hVm d)
          _ ≤ ENNReal.ofReal (A1 ^ d) * ENNReal.ofReal A1 := mul_le_mul' (ih j) (hmom d)
          _ = ENNReal.ofReal (A1 ^ (d + 1)) := by
              rw [← ENNReal.ofReal_mul (pow_nonneg hA0 _), pow_succ]
      · calc _ ≤ ∫⁻ x, ENNReal.ofReal (exp (6 * l * trq c d (fun k => x (Sum.inl k)))) *
                {x | OnX m0 c d x}.indicator (fun x => ENNReal.ofReal
                (exp (l * PX m0 d x j + 3 * l * tpq m0 d x))) (fun k => x (Sum.inr k))
                ∂(Measure.pi fun _ : Idx (d + 1) => F) :=
              lintegral_mono fun x => by
                have := key x j (Or.inr rfl); rwa [if_neg (by simp)] at this
          _ = _ := split_int F d (hVm d) (hUm d j)
          _ ≤ ENNReal.ofReal A1 * ENNReal.ofReal (A1 ^ d) := mul_le_mul' (hmom d) (ih j)
          _ = ENNReal.ofReal (A1 ^ (d + 1)) := by
              rw [← ENNReal.ofReal_mul hA0, pow_succ, mul_comm]
    · -- m0 = d
      subst h
      have hpt : ∀ x : Idx (m0 + 1) → ℝ, {x | OnX m0 c (m0 + 1) x}.indicator
          (fun x => ENNReal.ofReal (exp (l * PX m0 (m0 + 1) x i + 3 * l * tpq m0 (m0 + 1) x))) x ≤
          ENNReal.ofReal (exp (6 * l * trq c (m0 + 1) x)) := by
        intro x
        by_cases hx : OnX m0 c (m0 + 1) x
        · rw [Set.indicator_of_mem (show x ∈ {x | OnX m0 c (m0 + 1) x} from hx)]
          apply ENNReal.ofReal_le_ofReal; apply Real.exp_le_exp.2
          have hS := hx.1 le_rfl
          have hq : 0 ≤ (∑ k, x k) ^ 2 / 2 ^ (m0 + 1) := by positivity
          have hPX : PX m0 (m0 + 1) x i = (∑ k, x k) ^ 2 / 2 ^ (m0 + 1) := by
            rcases i with j | j
            · show (if m0 ≤ m0 then _ else _) + _ = _
              rw [if_pos le_rfl, PX_eq_zero m0 m0 le_rfl, add_zero]
            · show (if m0 ≤ m0 then _ else _) + _ = _
              rw [if_pos le_rfl, PX_eq_zero m0 m0 le_rfl, add_zero]
          rw [hPX, tpq, if_pos (by omega), trq, if_pos hS]
          first | linarith [mul_nonneg hl hq] | nlinarith
        · rw [Set.indicator_of_notMem (show x ∉ {x | OnX m0 c (m0 + 1) x} from hx)]
          exact bot_le
      calc _ ≤ ∫⁻ x, ENNReal.ofReal (exp (6 * l * trq c (m0 + 1) x))
              ∂(Measure.pi fun _ : Idx (m0 + 1) => F) := lintegral_mono hpt
        _ ≤ ENNReal.ofReal A1 := hmom (m0 + 1)
        _ ≤ ENNReal.ofReal (A1 ^ (m0 + 1)) :=
            ENNReal.ofReal_le_ofReal (le_self_pow₀ hA1 (by omega))
    · -- d < m0: everything vanishes
      calc _ ≤ ∫⁻ _x, (1 : ℝ≥0∞) ∂(Measure.pi fun _ : Idx (d + 1) => F) :=
            lintegral_mono fun x => hle1 (d + 1) i x (PX_eq_zero m0 (d + 1) (by omega) x i)
              (by rw [tpq, if_neg (by omega)])
        _ = 1 := by simp
        _ ≤ ENNReal.ofReal (A1 ^ (d + 1)) := by
            rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hA1)

end P99bcb804

end X77_Kx5

section X78_Kx6

/-! R4 / Kx6 (Q7 moments and bad events): `mom_on` (exponential moment of the truncated
normalised square for smoothed leaves, constant `Amom`), the half-restriction maps are measure
preserving (`mp_left`, `mp_right`, `mpZ_left`, `mpZ_right`), and the off-range probabilities
`notOnX` (`≤ (2^n - 1)·2e^{-c²2^m0/12}`) and `notOnZ` (`≤ (2^n - 1)·2e^{-ε²2^m0/4}`). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma trq_nonneg (c : ℝ) (d : ℕ) (x : Idx d → ℝ) : 0 ≤ trq c d x := by
  unfold trq; split_ifs
  · positivity
  · exact le_refl _

/-- The moment constant produced by `mgf_of_tail` (a = 0, C = 1, c = 1/12, A = 2). -/
noncomputable def Amom : ℝ :=
  exp (1 / 12 / (2 * 1) * (0 + 1)) + 2 * exp (1 / 12 / (2 * 1) * (0 + 2 * 1)) /
    (1 - exp (-(1 / 12 / 2)))

lemma one_le_Amom : 1 ≤ Amom := by
  unfold Amom
  have h1 : 1 ≤ exp (1 / 12 / (2 * 1) * (0 + 1)) := Real.one_le_exp (by norm_num)
  have h2 : 0 < 1 - exp (-(1 / 12 / 2 : ℝ)) := by
    have : exp (-(1 / 12 / 2 : ℝ)) < 1 := by
      have h := Real.exp_lt_exp.2 (show -(1 / 12 / 2 : ℝ) < 0 by norm_num)
      rwa [Real.exp_zero] at h
    linarith
  have h3 : 0 ≤ 2 * exp (1 / 12 / (2 * 1) * (0 + 2 * 1)) / (1 - exp (-(1 / 12 / 2 : ℝ))) := by
    positivity
  linarith

lemma mp_left (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    MeasurePreserving (fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inl j))
      (Measure.pi fun _ : Idx (n + 1) => F) (Measure.pi fun _ : Idx n => F) := by
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => F)
  have h2 : MeasurePreserving Prod.fst ((Measure.pi fun _ : Idx n => F).prod
      (Measure.pi fun _ : Idx n => F)) (Measure.pi fun _ : Idx n => F) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod]; simp⟩
  exact h2.comp hmp

lemma mp_right (F : Measure ℝ) [IsProbabilityMeasure F] (n : ℕ) :
    MeasurePreserving (fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inr j))
      (Measure.pi fun _ : Idx (n + 1) => F) (Measure.pi fun _ : Idx n => F) := by
  have hmp := measurePreserving_sumPiEquivProdPi (fun _ : Idx n ⊕ Idx n => F)
  have h2 : MeasurePreserving Prod.snd ((Measure.pi fun _ : Idx n => F).prod
      (Measure.pi fun _ : Idx n => F)) (Measure.pi fun _ : Idx n => F) :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  exact h2.comp hmp

lemma mpZ_left (n : ℕ) : MeasurePreserving (fun z : Zn (n + 1) => z.2.1) (γZ (n + 1)) (γZ n) := by
  have := instProbγZ n
  have h1 : MeasurePreserving Prod.snd ((gaussianReal 0 1).prod ((γZ n).prod (γZ n)))
      ((γZ n).prod (γZ n)) := ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  have h2 : MeasurePreserving Prod.fst ((γZ n).prod (γZ n)) (γZ n) :=
    ⟨measurable_fst, by rw [Measure.map_fst_prod]; simp⟩
  exact h2.comp h1

lemma mpZ_right (n : ℕ) : MeasurePreserving (fun z : Zn (n + 1) => z.2.2) (γZ (n + 1)) (γZ n) := by
  have := instProbγZ n
  have h1 : MeasurePreserving Prod.snd ((gaussianReal 0 1).prod ((γZ n).prod (γZ n)))
      ((γZ n).prod (γZ n)) := ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  have h2 : MeasurePreserving Prod.snd ((γZ n).prod (γZ n)) (γZ n) :=
    ⟨measurable_snd, by rw [Measure.map_snd_prod]; simp⟩
  exact h2.comp h1

lemma measurableSet_OnZ (m0 : ℕ) (ε : ℝ) : ∀ n : ℕ, MeasurableSet {z : Zn n | OnZ m0 ε n z}
  | 0 => by
      have : {z : Zn 0 | OnZ m0 ε 0 z} = Set.univ := by ext z; simp [OnZ]
      rw [this]; exact MeasurableSet.univ
  | n + 1 => by
      have htop : MeasurableSet {z : Zn (n + 1) | m0 ≤ n → |z.1| ≤ ε * √((2 : ℝ) ^ (n + 1))} := by
        by_cases h : m0 ≤ n
        · simp only [h, true_implies]
          exact measurableSet_le (measurable_fst.abs) measurable_const
        · simp only [h, false_implies]
          exact MeasurableSet.univ
      have e : {z : Zn (n + 1) | OnZ m0 ε (n + 1) z} =
          {z : Zn (n + 1) | m0 ≤ n → |z.1| ≤ ε * √((2 : ℝ) ^ (n + 1))} ∩
            ((fun z : Zn (n + 1) => z.2.1) ⁻¹' {z : Zn n | OnZ m0 ε n z} ∩
              (fun z : Zn (n + 1) => z.2.2) ⁻¹' {z : Zn n | OnZ m0 ε n z}) := by
        ext z; rfl
      rw [e]
      exact htop.inter (((mpZ_left n).measurable (measurableSet_OnZ m0 ε n)).inter
        ((mpZ_right n).measurable (measurableSet_OnZ m0 ε n)))

lemma two_pow_sub_one_nonneg (n : ℕ) : (0 : ℝ) ≤ 2 ^ n - 1 := by
  have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  linarith

/-- Generic recursion for the bad-event bound on a dyadic tree. -/
lemma bad_rec {e P : ℝ≥0∞} {top L R : ℝ≥0∞} {k : ℝ} (hk : 0 ≤ k) (he : e = ENNReal.ofReal k)
    (hP : P ≤ top + L + R) (ht : top ≤ ENNReal.ofReal (2 * k)) (n : ℕ)
    (hL : L ≤ ENNReal.ofReal ((2 ^ n - 1) * (2 * k)))
    (hR : R ≤ ENNReal.ofReal ((2 ^ n - 1) * (2 * k))) :
    P ≤ ENNReal.ofReal ((2 ^ (n + 1) - 1) * (2 * k)) := by
  have h0 := two_pow_sub_one_nonneg n
  refine hP.trans ((add_le_add (add_le_add ht hL) hR).trans (le_of_eq ?_))
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  rw [pow_succ]; ring

section Kx6

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- Exponential moment of the truncated normalised square of smoothed block sums. -/
theorem mom_on (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {c : ℝ} (hc : c ≤ 6 * min t1 (1 / (B + 1))) {σ : ℝ} (hσ1 : |σ| ≤ 1) (d : ℕ) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : 6 * l ≤ 1 / 24) :
    ∫⁻ x, ENNReal.ofReal (exp (6 * l * trq c d x))
      ∂(Measure.pi fun _ : Idx d => sL G (Idx 0) σ) ≤ ENNReal.ofReal Amom := by
  set P := Measure.pi fun _ : Idx d => sL G (Idx 0) σ with hP
  have hN := card_Idx_pos d
  have hcard : (Fintype.card (Idx d) : ℝ) = 2 ^ d := by rw [card_Idx]; push_cast; ring
  have hpd : (0 : ℝ) < 2 ^ d := by positivity
  have htail : ∀ s : ℝ, 0 ≤ s → P {x | 0 + 1 * s < trq c d x} ≤
      ENNReal.ofReal (2 * exp (-(1 / 12 * s))) := by
    intro s hs
    set y := √(s * 2 ^ d) with hy
    have hsub : {x : Idx d → ℝ | 0 + 1 * s < trq c d x} ⊆
        {x | y < |∑ i, x i| ∧ |∑ i, x i| ≤ c * 2 ^ d} := by
      intro x hx
      have hx' : 0 + 1 * s < trq c d x := hx
      unfold trq at hx'
      split_ifs at hx' with h1
      · have hq : s * 2 ^ d < (∑ i, x i) ^ 2 := by
          rw [zero_add, one_mul, lt_div_iff₀ hpd] at hx'; exact hx'
        have hpos : 0 < |∑ i, x i| := by
          rw [abs_pos]; intro h0; rw [h0] at hq
          have : 0 ≤ s * 2 ^ d := by positivity
          simp at hq; linarith
        refine ⟨?_, h1⟩
        rw [hy, Real.sqrt_lt' hpos, sq_abs]; exact hq
      · linarith
    by_cases hyb : y ≤ 6 * min t1 (1 / (B + 1)) * Fintype.card (Idx d)
    · have ht := tail_abs ha0 hexp hm ht1 h2 hB hV hW (Idx d) hN hσ1 (Real.sqrt_nonneg _) hyb
      have hy2 : y ^ 2 = s * 2 ^ d := Real.sq_sqrt (by positivity)
      have e : y ^ 2 / (12 * Fintype.card (Idx d)) = 1 / 12 * s := by
        rw [hy2, hcard]; field_simp
      rw [e] at ht
      refine (measure_mono (hsub.trans fun x hx => hx.1)).trans (ht.trans (le_of_eq ?_))
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    · have hemp : {x : Idx d → ℝ | y < |∑ i, x i| ∧ |∑ i, x i| ≤ c * 2 ^ d} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
        intro h1
        rw [hcard] at hyb
        have : c * 2 ^ d ≤ 6 * min t1 (1 / (B + 1)) * 2 ^ d :=
          mul_le_mul_of_nonneg_right hc hpd.le
        linarith
      refine (measure_mono hsub).trans ?_
      rw [hemp, measure_empty]
      exact zero_le'
  have h := mgf_of_tail P (measurable_trq c d) (a := 0) (C := 1) (c := 1 / 12) (A := 2)
    one_pos (by norm_num) (by norm_num) htail
  refine le_trans (lintegral_mono fun x => ?_) h
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have := trq_nonneg c d x
  have e : (1 / 12 : ℝ) / (2 * 1) = 1 / 24 := by norm_num
  rw [e]
  first | linarith [mul_le_mul_of_nonneg_right hl this] | nlinarith

/-- Probability that some large block of smoothed leaves is off range. -/
theorem notOnX (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 6 * min t1 (1 / (B + 1))) {σ : ℝ} (hσ1 : |σ| ≤ 1) (m0 : ℕ) :
    ∀ n : ℕ, (Measure.pi fun _ : Idx n => sL G (Idx 0) σ) {x | ¬ OnX m0 c n x} ≤
      ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(c ^ 2 * 2 ^ m0 / 12))))
  | 0 => by
      have : {x : Idx 0 → ℝ | ¬ OnX m0 c 0 x} = ∅ := by ext x; simp [OnX]
      rw [this, measure_empty]; exact zero_le'
  | n + 1 => by
      have ih := notOnX ha0 hexp hm ht1 h2 hB hV hW hc0 hc hσ1 m0 n
      set k := exp (-(c ^ 2 * 2 ^ m0 / 12)) with hk
      have hsub : {x : Idx (n + 1) → ℝ | ¬ OnX m0 c (n + 1) x} ⊆
          {x | m0 ≤ n ∧ c * 2 ^ (n + 1) < |∑ i, x i|} ∪
            (fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inl j)) ⁻¹'
              {x | ¬ OnX m0 c n x} ∪
            (fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inr j)) ⁻¹'
              {x | ¬ OnX m0 c n x} := by
        intro x hx
        have hx' : ¬ ((m0 ≤ n → |∑ i, x i| ≤ c * 2 ^ (n + 1)) ∧
            OnX m0 c n (fun i => x (Sum.inl i)) ∧ OnX m0 c n (fun i => x (Sum.inr i))) := hx
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage]
        by_contra hcon
        push_neg at hcon
        exact hx' ⟨fun h => (hcon.1.1 h), hcon.1.2, hcon.2⟩
      have hL : (Measure.pi fun _ : Idx (n + 1) => sL G (Idx 0) σ)
          ((fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inl j)) ⁻¹' {x | ¬ OnX m0 c n x}) ≤
          ENNReal.ofReal ((2 ^ n - 1) * (2 * k)) := by
        rw [(mp_left _ n).measure_preimage (s := {x | ¬ OnX m0 c n x})
          (measurableSet_OnX m0 c n).compl.nullMeasurableSet]
        exact ih
      have hR : (Measure.pi fun _ : Idx (n + 1) => sL G (Idx 0) σ)
          ((fun x : Idx (n + 1) → ℝ => fun j : Idx n => x (Sum.inr j)) ⁻¹' {x | ¬ OnX m0 c n x}) ≤
          ENNReal.ofReal ((2 ^ n - 1) * (2 * k)) := by
        rw [(mp_right _ n).measure_preimage (s := {x | ¬ OnX m0 c n x})
          (measurableSet_OnX m0 c n).compl.nullMeasurableSet]
        exact ih
      refine bad_rec (exp_pos _).le rfl ((measure_mono hsub).trans
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))) ?_ n hL hR
      by_cases hmn : m0 ≤ n
      · have hN := card_Idx_pos (n + 1)
        have hcard : (Fintype.card (Idx (n + 1)) : ℝ) = 2 ^ (n + 1) := by
          rw [card_Idx]; push_cast; ring
        have hpd : (0 : ℝ) < 2 ^ (n + 1) := by positivity
        have hyb : c * 2 ^ (n + 1) ≤ 6 * min t1 (1 / (B + 1)) * Fintype.card (Idx (n + 1)) := by
          rw [hcard]; exact mul_le_mul_of_nonneg_right hc hpd.le
        have ht := tail_abs ha0 hexp hm ht1 h2 hB hV hW (Idx (n + 1)) hN hσ1
          (by positivity) hyb
        refine (measure_mono fun x hx => hx.2).trans (ht.trans ?_)
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have hm2 : (2 : ℝ) ^ m0 ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have e : (c * 2 ^ (n + 1)) ^ 2 / (12 * Fintype.card (Idx (n + 1))) =
            c ^ 2 * 2 ^ (n + 1) / 12 := by rw [hcard]; field_simp
        rw [e]
        have : c ^ 2 * 2 ^ m0 / 12 ≤ c ^ 2 * 2 ^ (n + 1) / 12 := by
          have := mul_le_mul_of_nonneg_left hm2 (sq_nonneg c); linarith
        have := Real.exp_le_exp.2 (neg_le_neg this)
        linarith
      · have : {x : Idx (n + 1) → ℝ | m0 ≤ n ∧ c * 2 ^ (n + 1) < |∑ i, x i|} = ∅ := by
          ext x; simp [hmn]
        rw [this, measure_empty]; exact zero_le'

/-- Probability that some large node Gaussian is off range. -/
theorem notOnZ {ε : ℝ} (hε : 0 ≤ ε) (m0 : ℕ) :
    ∀ n : ℕ, (γZ n) {z | ¬ OnZ m0 ε n z} ≤
      ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(1 / 4 * (ε ^ 2 * 2 ^ m0)))))
  | 0 => by
      have : {z : Zn 0 | ¬ OnZ m0 ε 0 z} = ∅ := by ext z; simp [OnZ]
      rw [this, measure_empty]; exact zero_le'
  | n + 1 => by
      have ih := notOnZ hε m0 n
      have := instProbγZ n
      have hsub : {z : Zn (n + 1) | ¬ OnZ m0 ε (n + 1) z} ⊆
          {z | m0 ≤ n ∧ ε * √((2 : ℝ) ^ (n + 1)) < |z.1|} ∪
            (fun z : Zn (n + 1) => z.2.1) ⁻¹' {z | ¬ OnZ m0 ε n z} ∪
            (fun z : Zn (n + 1) => z.2.2) ⁻¹' {z | ¬ OnZ m0 ε n z} := by
        intro z hz
        have hz' : ¬ ((m0 ≤ n → |z.1| ≤ ε * √((2 : ℝ) ^ (n + 1))) ∧
            OnZ m0 ε n z.2.1 ∧ OnZ m0 ε n z.2.2) := hz
        simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage]
        by_contra hcon
        push_neg at hcon
        exact hz' ⟨fun h => (hcon.1.1 h), hcon.1.2, hcon.2⟩
      have hL : (γZ (n + 1)) ((fun z : Zn (n + 1) => z.2.1) ⁻¹' {z | ¬ OnZ m0 ε n z}) ≤
          ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(1 / 4 * (ε ^ 2 * 2 ^ m0))))) := by
        rw [(mpZ_left n).measure_preimage (s := {z | ¬ OnZ m0 ε n z})
          (measurableSet_OnZ m0 ε n).compl.nullMeasurableSet]
        exact ih
      have hR : (γZ (n + 1)) ((fun z : Zn (n + 1) => z.2.2) ⁻¹' {z | ¬ OnZ m0 ε n z}) ≤
          ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(1 / 4 * (ε ^ 2 * 2 ^ m0))))) := by
        rw [(mpZ_right n).measure_preimage (s := {z | ¬ OnZ m0 ε n z})
          (measurableSet_OnZ m0 ε n).compl.nullMeasurableSet]
        exact ih
      refine bad_rec (exp_pos _).le rfl ((measure_mono hsub).trans
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl))) ?_ n hL hR
      by_cases hmn : m0 ≤ n
      · have hpd : (0 : ℝ) < 2 ^ (n + 1) := by positivity
        have hsub2 : {z : Zn (n + 1) | m0 ≤ n ∧ ε * √((2 : ℝ) ^ (n + 1)) < |z.1|} ⊆
            (fun z : Zn (n + 1) => z.1) ⁻¹' {w : ℝ | ε ^ 2 * 2 ^ (n + 1) < w ^ 2} := by
          intro z hz
          have h1 := hz.2
          have h0 : 0 ≤ ε * √((2 : ℝ) ^ (n + 1)) := by positivity
          have := mul_self_lt_mul_self h0 h1
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          rw [← sq_abs z.1]
          have e : (ε * √((2 : ℝ) ^ (n + 1))) * (ε * √((2 : ℝ) ^ (n + 1))) = ε ^ 2 * 2 ^ (n + 1) := by
            rw [mul_mul_mul_comm, Real.mul_self_sqrt hpd.le]; ring
          linarith
        have hmp1 : MeasurePreserving (fun z : Zn (n + 1) => z.1) (γZ (n + 1)) (gaussianReal 0 1) :=
          ⟨measurable_fst, by
            show ((gaussianReal 0 1).prod ((γZ n).prod (γZ n))).map Prod.fst = _
            rw [Measure.map_fst_prod]; simp⟩
        refine (measure_mono hsub2).trans ?_
        rw [hmp1.measure_preimage (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet]
        refine (gauss_tail _).trans ?_
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        have hm2 : (2 : ℝ) ^ m0 ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have : 1 / 4 * (ε ^ 2 * 2 ^ m0) ≤ 1 / 4 * (ε ^ 2 * 2 ^ (n + 1)) := by
          have := mul_le_mul_of_nonneg_left hm2 (sq_nonneg ε); linarith
        have := Real.exp_le_exp.2 (neg_le_neg this)
        linarith
      · have : {z : Zn (n + 1) | m0 ≤ n ∧ ε * √((2 : ℝ) ^ (n + 1)) < |z.1|} = ∅ := by
          ext z; simp [hmn]
        rw [this, measure_empty]; exact zero_le'

end Kx6

end P99bcb804

end X78_Kx6

section X79_Kx7

/-! R4 / Kx7 (Q7 crude cutoff-block moments): `momW` (exponential moment of the cutoff block
size `Wx` from a one-leaf absolute moment), `Ls_le` (`Ls u ≤ 3u²` near 0), `absmom_nu` and
`absmom_gauss` (one-leaf absolute exponential moments of smoothed and Gaussian leaves). -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma measurable_Wx (m0 : ℕ) : ∀ (n : ℕ) (i : Idx n), Measurable fun x : Idx n → ℝ => Wx m0 n x i
  | 0, _ => Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).abs
  | n + 1, i => by
      by_cases h : n + 1 ≤ m0
      · have e : (fun x : Idx (n + 1) → ℝ => Wx m0 (n + 1) x i) = fun x => ∑ j, |x j| := by
          funext x; exact if_pos h
        rw [e]; exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).abs
      · rcases i with i | i
        · have e : (fun x : Idx (n + 1) → ℝ => Wx m0 (n + 1) x (Sum.inl i)) =
              fun x => Wx m0 n (fun j => x (Sum.inl j)) i := by
            funext x; exact if_neg h
          rw [e]
          exact (measurable_Wx m0 n i).comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)
        · have e : (fun x : Idx (n + 1) → ℝ => Wx m0 (n + 1) x (Sum.inr i)) =
              fun x => Wx m0 n (fun j => x (Sum.inr j)) i := by
            funext x; exact if_neg h
          rw [e]
          exact (measurable_Wx m0 n i).comp (measurable_pi_lambda _ fun j => measurable_pi_apply _)

lemma lint_prod_abs (F : Measure ℝ) [IsProbabilityMeasure F] (ι : Type) [Fintype ι] (a : ℝ) :
    ∫⁻ x, ENNReal.ofReal (exp (a * ∑ i, |x i|)) ∂(Measure.pi fun _ : ι => F) =
      (∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂F) ^ Fintype.card ι := by
  have hm : Measurable fun y : ℝ => ENNReal.ofReal (exp (a * |y|)) := by fun_prop
  have e : (fun x : ι → ℝ => ENNReal.ofReal (exp (a * ∑ i, |x i|))) =
      fun x => ∏ i, ENNReal.ofReal (exp (a * |x i|)) := by
    funext x
    rw [Finset.mul_sum, Real.exp_sum, ENNReal.ofReal_prod_of_nonneg (fun i _ => (exp_pos _).le)]
  rw [e, lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → ℝ) => ENNReal.ofReal (exp (a * |x i|)))
    (iIndepFun_pi (μ := fun _ : ι => F) (X := fun _ => fun y => ENNReal.ofReal (exp (a * |y|)))
      (fun _ => hm.aemeasurable))
    (fun i => hm.comp (measurable_pi_apply i))]
  have e2 : ∀ i : ι, ∫⁻ x, ENNReal.ofReal (exp (a * |x i|)) ∂(Measure.pi fun _ : ι => F)
      = ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂F := fun i =>
    (measurePreserving_eval (fun _ : ι => F) i).lintegral_comp hm
  simp_rw [e2]
  rw [Finset.prod_const, Finset.card_univ]

/-- Exponential moment of the cutoff block size. -/
theorem momW (F : Measure ℝ) [IsProbabilityMeasure F] (m0 : ℕ) {a : ℝ} {E0 : ℝ≥0∞}
    (hE1 : 1 ≤ E0) (hF : ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂F ≤ E0) :
    ∀ (n : ℕ) (i : Idx n), ∫⁻ x, ENNReal.ofReal (exp (a * Wx m0 n x i))
      ∂(Measure.pi fun _ : Idx n => F) ≤ E0 ^ (2 ^ m0)
  | 0, i => by
      show ∫⁻ x, ENNReal.ofReal (exp (a * ∑ j, |x j|)) ∂(Measure.pi fun _ : Idx 0 => F) ≤ _
      rw [lint_prod_abs, card_Idx, pow_zero, pow_one]
      exact hF.trans (le_self_pow₀ hE1 (by positivity))
  | n + 1, i => by
      by_cases h : n + 1 ≤ m0
      · have e : (fun x : Idx (n + 1) → ℝ => ENNReal.ofReal (exp (a * Wx m0 (n + 1) x i))) =
            fun x => ENNReal.ofReal (exp (a * ∑ j, |x j|)) := by
          funext x; rw [show Wx m0 (n + 1) x i = ∑ j, |x j| from if_pos h]
        rw [e, lint_prod_abs, card_Idx]
        calc (∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂F) ^ 2 ^ (n + 1) ≤ E0 ^ 2 ^ (n + 1) :=
              pow_le_pow_left₀ zero_le' hF _
          _ ≤ E0 ^ 2 ^ m0 := pow_le_pow_right₀ hE1 (Nat.pow_le_pow_right (by norm_num) h)
      · rcases i with i | i
        · have e : (fun x : Idx (n + 1) → ℝ => ENNReal.ofReal (exp (a * Wx m0 (n + 1) x (Sum.inl i))))
              = (fun x : Idx n → ℝ => ENNReal.ofReal (exp (a * Wx m0 n x i))) ∘
                (fun x : Idx (n + 1) → ℝ => fun j => x (Sum.inl j)) := by
            funext x
            show _ = ENNReal.ofReal (exp (a * Wx m0 n (fun j => x (Sum.inl j)) i))
            rw [show Wx m0 (n + 1) x (Sum.inl i) = Wx m0 n (fun j => x (Sum.inl j)) i from if_neg h]
          have h1 : ∫⁻ x, (fun y : Idx n → ℝ => ENNReal.ofReal (exp (a * Wx m0 n y i)))
              (fun j => x (Sum.inl j)) ∂(Measure.pi fun _ : Idx (n + 1) => F) =
              ∫⁻ y, ENNReal.ofReal (exp (a * Wx m0 n y i)) ∂(Measure.pi fun _ : Idx n => F) :=
            (mp_left F n).lintegral_comp
              ((Real.measurable_exp.comp (measurable_const.mul (measurable_Wx m0 n i))).ennreal_ofReal)
          rw [e]
          exact (le_of_eq h1).trans (momW F m0 hE1 hF n i)
        · have e : (fun x : Idx (n + 1) → ℝ => ENNReal.ofReal (exp (a * Wx m0 (n + 1) x (Sum.inr i))))
              = (fun x : Idx n → ℝ => ENNReal.ofReal (exp (a * Wx m0 n x i))) ∘
                (fun x : Idx (n + 1) → ℝ => fun j => x (Sum.inr j)) := by
            funext x
            show _ = ENNReal.ofReal (exp (a * Wx m0 n (fun j => x (Sum.inr j)) i))
            rw [show Wx m0 (n + 1) x (Sum.inr i) = Wx m0 n (fun j => x (Sum.inr j)) i from if_neg h]
          have h1 : ∫⁻ x, (fun y : Idx n → ℝ => ENNReal.ofReal (exp (a * Wx m0 n y i)))
              (fun j => x (Sum.inr j)) ∂(Measure.pi fun _ : Idx (n + 1) => F) =
              ∫⁻ y, ENNReal.ofReal (exp (a * Wx m0 n y i)) ∂(Measure.pi fun _ : Idx n => F) :=
            (mp_right F n).lintegral_comp
              ((Real.measurable_exp.comp (measurable_const.mul (measurable_Wx m0 n i))).ennreal_ofReal)
          rw [e]
          exact (le_of_eq h1).trans (momW F m0 hE1 hF n i)

lemma exp_abs_le (a y : ℝ) :
    ENNReal.ofReal (exp (a * |y|)) ≤ ENNReal.ofReal (exp (a * y)) + ENNReal.ofReal (exp ((-a) * y)) := by
  rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rcases abs_cases y with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]; have := exp_pos ((-a) * y); linarith
  · rw [h, mul_neg, ← neg_mul]; have := exp_pos (a * y); linarith

lemma absmom_gauss (v : ℝ≥0) (a : ℝ) :
    ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂(gaussianReal 0 v) ≤
      2 * ENNReal.ofReal (exp (v * a ^ 2 / 2)) := by
  refine (lintegral_mono fun y => exp_abs_le a y).trans (le_of_eq ?_)
  rw [lintegral_add_left (by fun_prop), lmgf_gauss, lmgf_gauss, neg_sq, two_mul]

section Kx7

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma Ls_le (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {σ : ℝ} (hσ1 : |σ| ≤ 1) {u : ℝ} (hu : |u| ≤ min t1 (1 / (B + 1))) : Ls G σ u ≤ 3 * u ^ 2 := by
  have hu1 : |u| ≤ t1 := hu.trans (min_le_left _ _)
  have huB : B * |u| ≤ 1 := by
    have h := hu.trans (min_le_right _ _)
    have hB1 : 0 < B + 1 := by linarith
    rw [le_div_iff₀ hB1] at h
    linarith [abs_nonneg u]
  have hc := cgf_le ha0 hexp hm ht1 h2 hV hW hu1 huB
  have hσ2 : σ ^ 2 ≤ 1 := by
    have := sq_abs σ; nlinarith [abs_nonneg σ]
  rw [Ls]
  have : u ^ 2 * σ ^ 2 ≤ u ^ 2 := mul_le_of_le_one_right (sq_nonneg u) hσ2
  have := sq_nonneg u
  linarith

lemma absmom_nu (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {σ : ℝ} (hσ1 : |σ| ≤ 1) {a : ℝ} (ha : |a| ≤ min t1 (1 / (B + 1))) :
    ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂(sL G (Idx 0) σ) ≤
      2 * ENNReal.ofReal (exp (3 * a ^ 2)) := by
  have ha1 : |a| ≤ a0 := (ha.trans (min_le_left _ _)).trans (by linarith)
  have ha2 : |-a| ≤ a0 := by rw [abs_neg]; exact ha1
  refine (lintegral_mono fun y => exp_abs_le a y).trans ?_
  rw [lintegral_add_left (by fun_prop), lmgf_nu hexp σ ha1, lmgf_nu hexp σ ha2, two_mul]
  have h1 := Ls_le ha0 hexp hm ht1 h2 hB hV hW hσ1 ha
  have h2' := Ls_le ha0 hexp hm ht1 h2 hB hV hW hσ1 (u := -a) (by rw [abs_neg]; exact ha)
  rw [neg_sq] at h2'
  exact add_le_add (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h1))
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 h2'))

end Kx7

end P99bcb804

end X79_Kx7

section X80_Kx8

/-! R4 / Kx8 (Q7 node hypothesis): from the node quantile bound `node_κ` (as an abstract
hypothesis `H`) derive the `hnode` hypothesis of `DBc_le` for the smoothed split
`f m S z0 = qnt (κC G (Idx m) σ S) (Phi z0)` against the Gaussian split `gS l0`,
`l0 = √(L2s G σ 0)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

section Kx8

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma two_pow_succ_eq (m : ℕ) : 2 * (Fintype.card (Idx m) : ℝ) = (2 : ℝ) ^ (m + 1) := by
  rw [card_Idx]; push_cast; ring

theorem node_hyp {t1 C εq β N3 σ : ℝ} (hC : 0 < C) (hεq : 0 < εq) (hβ : 0 < β)
    (H : ∀ (ι : Type) [Fintype ι] (σ T : ℝ), 0 < σ → σ ≤ 1 → N3 ≤ (Fintype.card ι : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card ι) → |T| ≤ t1 / 4 * (2 * Fintype.card ι) →
        ∀ u : ℝ, |u| < εq * (2 * Fintype.card ι) →
          |qnt (κC G ι σ T) (Phi (u / (√(L2s G σ 0) * √(2 * (Fintype.card ι : ℝ))))) - u|
            ≤ C * (1 + u ^ 2 / (2 * Fintype.card ι) + T ^ 2 / (2 * Fintype.card ι)))
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hL : 1 / 2 ≤ L2s G σ 0 ∧ L2s G σ 0 ≤ 3)
    {m0 : ℕ} (hN3 : N3 ≤ (2 : ℝ) ^ m0) (hσβ : σ⁻¹ ≤ exp (β * (2 : ℝ) ^ m0)) :
    ∀ m, m0 ≤ m → ∀ S S' z0 : ℝ, |S| ≤ t1 / 4 * 2 ^ (m + 1) →
      |z0| ≤ εq / 4 * √((2 : ℝ) ^ (m + 1)) →
      |(fun n T z0 => qnt (κC G (Idx n) σ T) (Phi z0)) m S z0 - gS (√(L2s G σ 0)) m S' z0|
        ≤ (3 * C) * (1 + z0 ^ 2 + S ^ 2 / 2 ^ (m + 1)) := by
  intro m hm S S' z0 hS hz
  have hpow : (2 : ℝ) ^ m0 ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hcard : (Fintype.card (Idx m) : ℝ) = 2 ^ m := by rw [card_Idx]; push_cast; ring
  have hc2 := two_pow_succ_eq m
  set l0 := √(L2s G σ 0) with hl0
  have hl0p : 0 < l0 := Real.sqrt_pos.2 (by linarith only [hL.1])
  have hl0sq : l0 ^ 2 = L2s G σ 0 := Real.sq_sqrt (by linarith only [hL.1])
  have hl02 : l0 ≤ 2 := by
    by_contra hcon; push_neg at hcon
    have := mul_lt_mul hcon hcon.le (by norm_num) hl0p.le
    linarith only [this, hL.2, hl0sq]
  set q := √((2 : ℝ) ^ (m + 1)) with hq
  have hqp : 0 < q := Real.sqrt_pos.2 (by positivity)
  have hqsq : q ^ 2 = (2 : ℝ) ^ (m + 1) := Real.sq_sqrt (by positivity)
  set u := l0 * q * z0 with hu
  have hg : gS l0 m S' z0 = u := rfl
  have hdiv : u / (l0 * √(2 * (Fintype.card (Idx m) : ℝ))) = z0 := by
    rw [hc2, ← hq, hu]; field_simp
  have hN : N3 ≤ (Fintype.card (Idx m) : ℝ) := by rw [hcard]; linarith
  have hsb : σ⁻¹ ≤ exp (β * Fintype.card (Idx m)) := by
    rw [hcard]
    exact le_trans hσβ (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hpow hβ.le))
  have hT : |S| ≤ t1 / 4 * (2 * Fintype.card (Idx m)) := by rw [hc2]; exact hS
  have hu' : |u| < εq * (2 * Fintype.card (Idx m)) := by
    rw [hc2, hu, abs_mul, abs_mul, abs_of_pos hl0p, abs_of_pos hqp]
    have h1 : l0 * q * |z0| ≤ 2 * q * (εq / 4 * q) := by
      have := mul_le_mul hl02 hz (abs_nonneg z0) (by norm_num)
      have h' := mul_le_mul_of_nonneg_left this hqp.le
      linarith only [h']
    have h2 : 2 * q * (εq / 4 * q) = εq / 2 * 2 ^ (m + 1) := by rw [← hqsq]; ring
    have h3 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have h4 := mul_pos hεq h3
    linarith only [h1, h2, h4]
  have h := H (Idx m) σ S hσ0 hσ1 hN hsb hT u hu'
  rw [hdiv, hc2] at h
  show |qnt (κC G (Idx m) σ S) (Phi z0) - gS l0 m S' z0| ≤ _
  rw [hg]
  have e : u ^ 2 / 2 ^ (m + 1) = l0 ^ 2 * z0 ^ 2 := by
    rw [hu, ← hqsq]; field_simp
  rw [e, hl0sq] at h
  have hS2 : 0 ≤ S ^ 2 / 2 ^ (m + 1) := by positivity
  have hz2 := sq_nonneg z0
  have hk : L2s G σ 0 * z0 ^ 2 ≤ 3 * z0 ^ 2 := mul_le_mul_of_nonneg_right hL.2 hz2
  have hfin : 0 ≤ C * (2 + (3 * z0 ^ 2 - L2s G σ 0 * z0 ^ 2) + 2 * (S ^ 2 / 2 ^ (m + 1))) :=
    mul_nonneg hC.le (by linarith only [hk, hS2])
  linarith only [h, hfin]

end Kx8

end P99bcb804

end X80_Kx8

section X81_Kr2

/-! R4 / Kr2 (root density): the standardised root density `hR x = sR · fS(sR x)`,
`sR = √(N L2s 0)`: integrability and total mass, its law maps to `sL` (`hR_map`), the far tail
via `xLaw` + `tail_abs` (`hR_far`), and the scalar near conversion `root_near`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

noncomputable def sR (G : Measure ℝ) (ι : Type) [Fintype ι] (σ : ℝ) : ℝ :=
  √(Fintype.card ι * L2s G σ 0)

noncomputable def hR (G : Measure ℝ) (ι : Type) [Fintype ι] (σ x : ℝ) : ℝ :=
  sR G ι σ * fS G ι σ (sR G ι σ * x)

lemma near_sum_l {x q l : ℝ} (hq : 0 < q) (hl : 0 < l) (hl2 : l ≤ 2) :
    1 / q + l * |x| / q + q ^ 2 * (l * |x| / q) ^ 3 ≤ 11 * (1 / q) * (1 + |x| ^ 3) := by
  have hx0 := abs_nonneg x
  have e : 1 / q + l * |x| / q + q ^ 2 * (l * |x| / q) ^ 3
      = (1 / q) * (1 + l * |x| + l ^ 3 * |x| ^ 3) := by field_simp
  rw [e, mul_comm 11, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hl3 : l ^ 3 ≤ 8 := by
    calc l ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hl.le hl2 3
      _ = 8 := by norm_num
  have t4 : |x| ≤ 1 + |x| ^ 3 := by
    rcases le_total |x| 1 with h | h
    · linarith [pow_nonneg hx0 3]
    · have h2 : 1 ≤ |x| ^ 2 := one_le_pow₀ h
      have : |x| ≤ |x| ^ 3 := by
        calc |x| = |x| * 1 := (mul_one _).symm
          _ ≤ |x| * |x| ^ 2 := by gcongr
          _ = |x| ^ 3 := by ring
      linarith [pow_nonneg hx0 3]
  have h1 : l * |x| ≤ 2 * |x| := mul_le_mul_of_nonneg_right hl2 hx0
  have h3 : l ^ 3 * |x| ^ 3 ≤ 8 * |x| ^ 3 := mul_le_mul_of_nonneg_right hl3 (by positivity)
  linarith

/-- Scalar near conversion: from the single-factor local Cramér bound to the `DtHyp` near
bounds with `K0 = 1`, `ε = 1/√N`. -/
lemma root_near {K t1 ε0 N L : ℝ} (hK : 0 ≤ K) (hN : 0 < N) (hL1 : 1 / 2 ≤ L) (hL3 : L ≤ 3)
    (hε0 : ε0 ≤ t1 / 4) (f : ℝ → ℝ)
    (H : ∀ δ : ℝ, |δ| ≤ t1 / 2 →
      (√(2 * π * N))⁻¹ * (√L)⁻¹ * exp (-(N * δ ^ 2 / (2 * L))) *
          exp (-(K * (1 / √N + |δ| + N * |δ| ^ 3))) ≤ f (N * δ) ∧
        f (N * δ) ≤ (√(2 * π * N))⁻¹ * (√L)⁻¹ * exp (-(N * δ ^ 2 / (2 * L))) *
          exp (K * (1 / √N + |δ| + N * |δ| ^ 3)))
    (x : ℝ) (hx : |x| ≤ ε0 / (1 / √N)) :
    √(N * L) * f (√(N * L) * x) ≤ 1 * phi x * exp (11 * K * (1 / √N) * (1 + |x| ^ 3)) ∧
      1 * phi x * exp (-(11 * K * (1 / √N) * (1 + |x| ^ 3))) ≤ √(N * L) * f (√(N * L) * x) := by
  set q := √N with hqdef
  set l := √L with hldef
  have hq : 0 < q := Real.sqrt_pos.2 hN
  have hq2 : q ^ 2 = N := Real.sq_sqrt hN.le
  have hl : 0 < l := Real.sqrt_pos.2 (by linarith)
  have hl2 : l ^ 2 = L := Real.sq_sqrt (by linarith)
  have hl2' : l ≤ 2 := by
    by_contra hcon; push_neg at hcon
    have := mul_lt_mul hcon hcon.le (by norm_num) hl.le
    linarith only [this, hl2, hL3]
  have hs : √(N * L) = q * l := Real.sqrt_mul hN.le L
  set δ := l * x / q with hδdef
  have hx' : |x| ≤ ε0 * q := by rwa [div_div_eq_mul_div, div_one] at hx
  have habs : |δ| = l * |x| / q := by
    rw [hδdef, abs_div, abs_mul, abs_of_pos hl, abs_of_pos hq]
  have hδ : |δ| ≤ t1 / 2 := by
    rw [habs, div_le_iff₀ hq]
    have h1 : l * |x| ≤ 2 * (ε0 * q) := mul_le_mul hl2' hx' (abs_nonneg x) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right hε0 hq.le
    linarith only [h1, h2]
  have e1 : N * δ = √(N * L) * x := by
    rw [hs, hδdef, ← hq2]; field_simp
  have e3 : N * δ ^ 2 / (2 * L) = x ^ 2 / 2 := by
    rw [hδdef, ← hl2, ← hq2]; field_simp
  have e0 : √(N * L) * ((√(2 * π * N))⁻¹ * (√L)⁻¹) = (√(2 * π))⁻¹ := by
    rw [hs, Real.sqrt_mul (by positivity) N, ← hqdef, ← hldef]
    field_simp
  have hbd : K * (1 / √N + |δ| + N * |δ| ^ 3) ≤ 11 * K * (1 / √N) * (1 + |x| ^ 3) := by
    rw [← hqdef, habs, ← hq2]
    have := mul_le_mul_of_nonneg_left (near_sum_l (x := x) hq hl hl2') hK
    linarith
  obtain ⟨hlo, hup⟩ := H δ hδ
  rw [e1, e3] at hlo hup
  have hs0 : 0 ≤ √(N * L) := Real.sqrt_nonneg _
  have hphi : phi x = (√(2 * π))⁻¹ * exp (-(x ^ 2 / 2)) := rfl
  constructor
  · calc √(N * L) * f (√(N * L) * x)
        ≤ √(N * L) * ((√(2 * π * N))⁻¹ * (√L)⁻¹ * exp (-(x ^ 2 / 2)) *
            exp (K * (1 / √N + |δ| + N * |δ| ^ 3))) := mul_le_mul_of_nonneg_left hup hs0
      _ = phi x * exp (K * (1 / √N + |δ| + N * |δ| ^ 3)) := by
          rw [hphi, ← e0]; ring
      _ ≤ 1 * phi x * exp (11 * K * (1 / √N) * (1 + |x| ^ 3)) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.2 hbd) (by unfold phi; positivity)
  · calc 1 * phi x * exp (-(11 * K * (1 / √N) * (1 + |x| ^ 3)))
        ≤ phi x * exp (-(K * (1 / √N + |δ| + N * |δ| ^ 3))) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg hbd))
            (by unfold phi; positivity)
      _ = √(N * L) * ((√(2 * π * N))⁻¹ * (√L)⁻¹ * exp (-(x ^ 2 / 2)) *
            exp (-(K * (1 / √N + |δ| + N * |δ| ^ 3)))) := by
          rw [hphi, ← e0]; ring
      _ ≤ √(N * L) * f (√(N * L) * x) := mul_le_mul_of_nonneg_left hlo hs0

section Kr2

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma hR_nonneg (ι : Type) [Fintype ι] (σ x : ℝ) : 0 ≤ hR G ι σ x :=
  mul_nonneg (Real.sqrt_nonneg _) (fS_nonneg _ _ _)

lemma hR_int (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι)
    (hs : 0 < sR G ι σ) : Integrable (hR G ι σ) ∧ ∫ x, hR G ι σ x = 1 := by
  obtain ⟨hi, h1⟩ := fS_integrable (G := G) ι hσ hN
  have hc : Integrable (fun x => fS G ι σ (sR G ι σ * x)) := hi.comp_mul_left' hs.ne'
  refine ⟨hc.const_mul (sR G ι σ), ?_⟩
  unfold hR
  rw [integral_const_mul, Measure.integral_comp_mul_left, h1, smul_eq_mul, mul_one,
    abs_inv, abs_of_pos hs, mul_inv_cancel₀ hs.ne']

lemma hR_map (ι : Type) [Fintype ι] {σ : ℝ} (hσ : σ ≠ 0) (hN : 0 < Fintype.card ι)
    (hs : 0 < sR G ι σ) :
    (volume.withDensity (fun x => ENNReal.ofReal (hR G ι σ x))).map
      (fun x => sR G ι σ * x) = sL G ι σ := by
  rw [sL_dens ι hσ hN]
  set s := sR G ι σ with hsdef
  have hc1 : ENNReal.ofReal (1 / s) * ENNReal.ofReal s = 1 := by
    rw [← ENNReal.ofReal_mul (one_div_pos.2 hs).le, one_div_mul_cancel hs.ne', ENNReal.ofReal_one]
  ext B hB
  have hH : Measurable (B.indicator (fun a => ENNReal.ofReal (fS G ι σ a))) :=
    (fS_meas ι σ).ennreal_ofReal.indicator hB
  have hpt : ∀ x, ((fun x => s * x) ⁻¹' B).indicator (fun x => ENNReal.ofReal (hR G ι σ x)) x
      = B.indicator (fun a => ENNReal.ofReal (fS G ι σ a)) (s * x) * ENNReal.ofReal s := by
    intro x
    by_cases hx : s * x ∈ B
    · have hx' : x ∈ (fun x => s * x) ⁻¹' B := hx
      rw [indicator_of_mem hx', indicator_of_mem hx, hR, ← hsdef, ENNReal.ofReal_mul hs.le]
      ring
    · simp [Set.indicator, hx]
  rw [Measure.map_apply (measurable_const_mul _) hB, withDensity_apply _ (measurable_const_mul _ hB),
    withDensity_apply _ hB, ← lintegral_indicator (measurable_const_mul _ hB),
    ← lintegral_indicator hB, lintegral_congr hpt,
    lintegral_mul_const _ (show Measurable (fun x =>
      B.indicator (fun a => ENNReal.ofReal (fS G ι σ a)) (s * x))
      from hH.comp (measurable_const_mul _)),
    lint_scale _ hH hs, mul_right_comm, hc1, one_mul]

lemma sL_tail (n : ℕ) {σ : ℝ} (hσ : σ ≠ 0) (y : ℝ) :
    sL G (Idx n) σ {T | y < |T|} =
      (Measure.pi fun _ : Idx n => sL G (Idx 0) σ) {x | y < |∑ i, x i|} := by
  have hmp := xLaw (G := G) hσ n
  have hS : MeasurableSet {x : Idx n → ℝ | y < |∑ i, x i|} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [← hmp.map_eq, Measure.map_apply hmp.measurable hS]
  have e : (fun p : ℝ × Zn n => XT G σ n p.1 p.2) ⁻¹' {x | y < |∑ i, x i|}
      = {T : ℝ | y < |T|} ×ˢ (univ : Set (Zn n)) := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    rw [XT, sum_Bld]
  rw [e, Measure.prod_prod, measure_univ, mul_one]

end Kr2

end P99bcb804

end X81_Kr2

section X82_Kr3

/-! R4 / Kr3 (root Tusnady): far tail of the root density (`hR_far`), `DtHyp` for the root
density with `K0 = 1` (`root_dthyp`), and the root quantile bound (`root_qnt`):
`|qnt (sL G (Idx n) σ) (Φ(w/√N)) - √(L2s 0) w| <= C(1 + w²/N)` for `|w| < εr N`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Kr3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma far_exp_l {N L ε0 : ℝ} (hN : 0 < N) (hL : 1 / 2 ≤ L) :
    exp (-((√(N * L) * (ε0 / (1 / √N))) ^ 2 / (12 * N))) ≤
      exp (-((ε0 ^ 2 / 24) / (1 / √N) ^ 2)) := by
  apply exp_le_exp.2
  have hq2 : √N ^ 2 = N := Real.sq_sqrt hN.le
  have hs2 : √(N * L) ^ 2 = N * L := Real.sq_sqrt (mul_nonneg hN.le (by linarith only [hL]))
  have e1 : (√(N * L) * (ε0 / (1 / √N))) ^ 2 / (12 * N) = L * ε0 ^ 2 * N / 12 := by
    rw [div_div_eq_mul_div, div_one, mul_pow, mul_pow, hs2, hq2]; field_simp
  have e2 : (ε0 ^ 2 / 24) / (1 / √N) ^ 2 = ε0 ^ 2 * N / 24 := by
    rw [div_pow, one_pow, hq2]; field_simp
  rw [e1, e2]
  have : 0 ≤ ε0 ^ 2 * N := by positivity
  have h := mul_le_mul_of_nonneg_right hL this
  first | linarith only [h] | nlinarith

lemma far_y_l {N L ε0 m : ℝ} (hN : 0 < N) (hL3 : L ≤ 3) (hL : 1 / 2 ≤ L) (hε0 : 0 ≤ ε0)
    (hm : ε0 ≤ 3 * m) :
    √(N * L) * (ε0 / (1 / √N)) ≤ 6 * m * N := by
  have hq : √(N * L) * √N = N * √L := by
    rw [Real.sqrt_mul hN.le, mul_comm (√N), mul_assoc, Real.mul_self_sqrt hN.le, mul_comm]
  have hl2 : √L ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  rw [div_div_eq_mul_div, div_one, ← mul_assoc, mul_right_comm, hq]
  have h1 : N * √L * ε0 ≤ N * 2 * ε0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl2 hN.le) hε0
  nlinarith

theorem hR_far (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (n : ℕ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hε0t : ε0 ≤ 3 * min t1 (1 / (B + 1))) :
    ∫ x in (Icc (-(ε0 / (1 / √(Fintype.card (Idx n) : ℝ))))
        (ε0 / (1 / √(Fintype.card (Idx n) : ℝ))))ᶜ, hR G (Idx n) σ x
      ≤ 2 * exp (-((ε0 ^ 2 / 24) / (1 / √(Fintype.card (Idx n) : ℝ)) ^ 2)) := by
  set N : ℝ := (Fintype.card (Idx n) : ℝ) with hNdef
  have hN0 : 0 < Fintype.card (Idx n) := card_Idx_pos n
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hN0
  have hL := L2s_bd hV hσ0 hσ1 (t := 0) (by simp [ht1.le])
  set L := L2s G σ 0 with hLdef
  have hs : 0 < sR G (Idx n) σ := Real.sqrt_pos.2 (mul_pos hN (by linarith only [hL.1]))
  have hsN : sR G (Idx n) σ = √(N * L) := rfl
  set s := sR G (Idx n) σ with hsdef
  set r := ε0 / (1 / √N) with hr
  have hint := hR_int (G := G) (Idx n) hσ0.ne' hN0 hs
  have hS : MeasurableSet ((Icc (-r) r)ᶜ) := measurableSet_Icc.compl
  have hpre : (fun x => s * x) ⁻¹' (Icc (-(s * r)) (s * r))ᶜ = (Icc (-r) r)ᶜ := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_Icc, ← abs_le]
    rw [abs_mul, abs_of_pos hs]
    exact not_congr ⟨fun h => le_of_mul_le_mul_left h hs, fun h => mul_le_mul_of_nonneg_left h hs.le⟩
  have hset : (Icc (-(s * r)) (s * r))ᶜ = {T : ℝ | s * r < |T|} := by
    ext T; simp only [mem_compl_iff, mem_Icc, ← abs_le, not_le, mem_ofPred_eq]
  have hS2 : MeasurableSet ((Icc (-(s * r)) (s * r))ᶜ) := measurableSet_Icc.compl
  rw [← dens_real (hR_nonneg (Idx n) σ) hint.1 hS, ← hpre, ← map_real _ hS2,
    hR_map (Idx n) hσ0.ne' hN0 hs, hset, measureReal_def, sL_tail n hσ0.ne']
  have hy0 : 0 ≤ s * r := by positivity
  have hy : s * r ≤ 6 * min t1 (1 / (B + 1)) * Fintype.card (Idx n) := by
    rw [← hNdef, hsN, hr]
    exact far_y_l hN hL.2 hL.1 hε0.le hε0t
  have ht := tail_abs ha0 hexp hm ht1 h2 hB hV hW (Idx n) hN0 (σ := σ)
    (by rw [abs_of_pos hσ0]; exact hσ1) hy0 hy
  rw [← hNdef] at ht
  have h2e : (2 : ℝ≥0∞) * ENNReal.ofReal (exp (-((s * r) ^ 2 / (12 * N))))
      = ENNReal.ofReal (2 * exp (-((s * r) ^ 2 / (12 * N)))) := by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp
  rw [h2e] at ht
  refine le_trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ht) ?_
  rw [hsN, hr]
  exact mul_le_mul_of_nonneg_left (far_exp_l hN hL.1) (by norm_num)

theorem root_dthyp (ha0 : 0 < a0)
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
      ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 → N2 ≤ (Fintype.card (Idx n) : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card (Idx n)) →
        DtHyp c0 ε0 A b (hR G (Idx n) σ) 1 (1 / √(Fintype.card (Idx n) : ℝ)) := by
  obtain ⟨κ', K, N1, hκ0, hκ1, hK, H⟩ :=
    near_single ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  set c0 := 11 * K with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set ε0 := min (min (t1 / 4) (3 * min t1 (1 / (B + 1)))) (1 / (16 * (c0 + 1))) with hε0
  have hmin : 0 < min t1 (1 / (B + 1)) := lt_min ht1 (by positivity)
  have hε0p : 0 < ε0 := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hε0a : ε0 ≤ t1 / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hε0b : ε0 ≤ 3 * min t1 (1 / (B + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hε0c : ε0 ≤ 1 / (16 * (c0 + 1)) := min_le_right _ _
  have hce : c0 * ε0 ≤ 1 / 16 := by
    have h1 : c0 * ε0 ≤ c0 * (1 / (16 * (c0 + 1))) := mul_le_mul_of_nonneg_left hε0c hc00
    have h2' : c0 * (1 / (16 * (c0 + 1))) ≤ 1 / 16 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  refine ⟨c0, ε0, 2, ε0 ^ 2 / 24, κ' / 2, max N1 (max 2 (8 * exp κ' / κ' ^ 2)), hc00, hε0p, hce,
    by norm_num, by positivity, by positivity, ?_⟩
  intro n σ hσ hσ1 hN2 hσβ
  set N : ℝ := (Fintype.card (Idx n) : ℝ) with hNdef
  have hN0 : 0 < Fintype.card (Idx n) := card_Idx_pos n
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast hN0
  have hNN1 : N1 ≤ N := (le_max_left _ _).trans hN2
  have hN2r : (2 : ℝ) ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN2
  have hN8 : 8 * exp κ' / κ' ^ 2 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN2
  have hNnat : 2 ≤ Fintype.card (Idx n) := by
    have h := hN2r; rw [hNdef] at h; exact_mod_cast h
  have hκN := kappa_cond hκ0 hκ1 (Fintype.card (Idx n)) hN8 hNnat σ hσ hσβ
  have hL := L2s_bd hV hσ hσ1 (t := 0) (by simp [ht1.le])
  have hs : 0 < sR G (Idx n) σ := Real.sqrt_pos.2 (mul_pos hN (by linarith only [hL.1]))
  have hint := hR_int (G := G) (Idx n) hσ.ne' hN0 hs
  have HN := fun δ (hδ : |δ| ≤ t1 / 2) => H (Idx n) σ δ hσ hσ1 hNN1 hNnat hκN hδ
  refine ⟨by positivity, one_pos, hR_nonneg (Idx n) σ, hint.1, hint.2, ?_, ?_, ?_⟩
  · intro x hx
    exact (root_near hK hN hL.1 hL.2 hε0a (fS G (Idx n) σ) HN x hx).1
  · intro x hx
    exact (root_near hK hN hL.1 hL.2 hε0a (fS G (Idx n) σ) HN x hx).2
  · exact hR_far ha0 hexp hm ht1 h2 hB hV hW n hσ hσ1 hε0p hε0b

end Kr3

end P99bcb804

end X82_Kr3

section X83_Kr4

/-! R4 / Kr4 (root quantile): `root_qnt`:
`|qnt (sL G (Idx n) σ) (Φ(w/√N)) - √(L2s G σ 0) · w| <= C(1 + w²/N)` for `|w| < εr N`,
`N = card (Idx n)`, under `0<σ<=1`, `N2 <= N`, `σ⁻¹ <= e^{βN}`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Kr4

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

theorem root_qnt (ha0 : 0 < a0)
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
    ∃ C εr β N2 : ℝ, 0 < C ∧ 0 < εr ∧ 0 < β ∧
      ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 → N2 ≤ (Fintype.card (Idx n) : ℝ) →
        σ⁻¹ ≤ exp (β * Fintype.card (Idx n)) →
        ∀ w : ℝ, |w| < εr * Fintype.card (Idx n) →
          |qnt (sL G (Idx n) σ) (Phi (w / √(Fintype.card (Idx n) : ℝ))) - √(L2s G σ 0) * w|
            ≤ C * (1 + w ^ 2 / Fintype.card (Idx n)) := by
  obtain ⟨c0, ε0, A, b, β, N2, hc0, hε0, hce, hA, hb, hβ, HD⟩ :=
    root_dthyp ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  obtain ⟨c, εt, m₀, hc, hεt, hm₀, HT⟩ := dt_tusnady hc0 hε0 hce hA hb
  refine ⟨2 * c, εt, β, max N2 m₀, by positivity, hεt, hβ, ?_⟩
  intro n σ hσ hσ1 hN hσβ w hw
  have hN0 : 0 < Fintype.card (Idx n) := card_Idx_pos n
  have hNr : (0 : ℝ) < Fintype.card (Idx n) := by exact_mod_cast hN0
  have hmM : m₀ ≤ Fintype.card (Idx n) := by
    have h := (le_max_right _ _).trans hN; exact_mod_cast h
  have hD := HD n σ hσ hσ1 ((le_max_left _ _).trans hN) hσβ
  have hT := HT _ hmM (hR G (Idx n) σ) 1 hD
  obtain ⟨-, -, h0, hi, h1, -⟩ := hD
  have hwd := dens_prob h0 hi h1
  obtain ⟨L, hLdef⟩ : ∃ L : Measure ℝ, L = (volume.withDensity
      (fun x => ENNReal.ofReal (hR G (Idx n) σ x))).map
      (fun x => √(Fintype.card (Idx n) : ℝ) * x) := ⟨_, rfl⟩
  haveI : IsProbabilityMeasure L := by
    rw [hLdef]; exact Measure.isProbabilityMeasure_map (measurable_const_mul _).aemeasurable
  rw [← hLdef] at hT
  have hsq : 0 < √(Fintype.card (Idx n) : ℝ) := Real.sqrt_pos.2 hNr
  have hq := qnt_close L hsq (fun y => c * (1 + y ^ 2 / Fintype.card (Idx n))) (by fun_prop)
    hT hw
  have hL := L2s_bd hV hσ hσ1 (t := 0) (by simp [ht1.le])
  have hl0 : 0 < √(L2s G σ 0) := Real.sqrt_pos.2 (by linarith only [hL.1])
  have hl2 : √(L2s G σ 0) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [hL.2]
  have hs : 0 < sR G (Idx n) σ := Real.sqrt_pos.2 (mul_pos hNr (by linarith only [hL.1]))
  have hmapL : sL G (Idx n) σ = L.map (fun x => √(L2s G σ 0) * x) := by
    rw [← hR_map (Idx n) hσ.ne' hN0 hs, hLdef,
      Measure.map_map (measurable_const_mul _) (measurable_const_mul _)]
    congr 1
    funext x
    simp only [Function.comp_apply]
    rw [sR, Real.sqrt_mul hNr.le]; ring
  rw [hmapL, qnt_map_mul L hl0 (Phi_pos' _) (Phi_lt_one _), ← mul_sub, abs_mul,
    abs_of_pos hl0]
  have hδ0 : 0 ≤ c * (1 + w ^ 2 / Fintype.card (Idx n)) := by positivity
  calc √(L2s G σ 0) * |qnt L (Phi (w / √(Fintype.card (Idx n) : ℝ))) - w|
      ≤ 2 * (c * (1 + w ^ 2 / Fintype.card (Idx n))) :=
        mul_le_mul hl2 hq (abs_nonneg _) (by norm_num)
    _ = 2 * c * (1 + w ^ 2 / Fintype.card (Idx n)) := by ring

end Kr4

end P99bcb804

end X83_Kr4

section X84_Kb1

/-! R4 / Kb1 (block coupling, construction): root Gaussian `w ~ N(0,1)` and node Gaussians
`z ~ γZ n`; X side `XT G σ n (qnt (sL G (Idx n) σ) (Φ w)) z` (iid `sL G (Idx 0) σ`),
Y side `l · G n (√(2^n) w) z` (iid `N(0,1)` scaled by `l`). Marginals `cpl_fst`, `cpl_snd`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Kb1

variable {G : Measure ℝ} [IsProbabilityMeasure G]

/-- Root total of the X side. -/
noncomputable def Tq (G : Measure ℝ) (σ : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  qnt (sL G (Idx n) σ) (Phi w)

noncomputable def cplX (G : Measure ℝ) (σ : ℝ) (n : ℕ) (q : ℝ × Zn n) : Idx n → ℝ :=
  XT G σ n (Tq G σ n q.1) q.2

noncomputable def cplY (l : ℝ) (n : ℕ) (q : ℝ × Zn n) : Idx n → ℝ :=
  fun i => l * P99bcb804.G n (√((2 : ℝ) ^ n) * q.1) q.2 i

noncomputable def cplQ (G : Measure ℝ) (σ l : ℝ) (n : ℕ) :
    Measure ((Idx n → ℝ) × (Idx n → ℝ)) :=
  ((gaussianReal 0 1).prod (γZ n)).map (fun q => (cplX G σ n q, cplY l n q))

lemma measurable_Tq (σ : ℝ) (n : ℕ) : Measurable (Tq G σ n) := by
  have h := measurable_qnt_Phi (sL G (Idx n) σ) (s := 1)
  have e : (fun w => qnt (sL G (Idx n) σ) (Phi (w / 1))) = Tq G σ n := by
    funext w; simp [Tq]
  rwa [e] at h

lemma measurable_cplX {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) : Measurable (cplX G σ n) :=
  (measurable_XT hσ n).comp (((measurable_Tq σ n).comp measurable_fst).prodMk measurable_snd)

lemma measurable_cplY (l : ℝ) (n : ℕ) : Measurable (cplY l n) := by
  have hG : Measurable fun q : ℝ × Zn n => P99bcb804.G n (√((2 : ℝ) ^ n) * q.1) q.2 :=
    (measurable_G n).comp ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  exact measurable_pi_lambda _ fun i => measurable_const.mul ((measurable_pi_apply i).comp hG)

theorem cpl_fst {σ : ℝ} (hσ : σ ≠ 0) (l : ℝ) (n : ℕ) :
    (cplQ G σ l n).map Prod.fst = Measure.pi fun _ : Idx n => sL G (Idx 0) σ := by
  have hX := measurable_cplX (G := G) hσ n
  have hY := measurable_cplY l n
  have hP : Measurable (Prod.map (Tq G σ n) (id : Zn n → Zn n)) :=
    (measurable_Tq σ n).prodMap measurable_id
  rw [cplQ, Measure.map_map measurable_fst (hX.prodMk hY)]
  have e : (Prod.fst ∘ fun q : ℝ × Zn n => (cplX G σ n q, cplY l n q)) =
      (fun p : ℝ × Zn n => XT G σ n p.1 p.2) ∘ Prod.map (Tq G σ n) id := rfl
  rw [e, ← Measure.map_map (measurable_XT hσ n) hP,
    ← Measure.map_prod_map _ _ (measurable_Tq σ n) measurable_id, Measure.map_id]
  have hT : (gaussianReal 0 1).map (Tq G σ n) = sL G (Idx n) σ := map_qnt_Phi' _
  rw [hT]
  exact (xLaw hσ n).map_eq

theorem cpl_snd {σ : ℝ} (hσ : σ ≠ 0) (l : ℝ) (n : ℕ) :
    (cplQ G σ l n).map Prod.snd =
      Measure.pi fun _ : Idx n => (gaussianReal 0 1).map (fun y => l * y) := by
  have hX := measurable_cplX (G := G) hσ n
  have hY := measurable_cplY l n
  have hW : Measurable (Prod.map (fun w : ℝ => √((2 : ℝ) ^ n) * w) (id : Zn n → Zn n)) :=
    (measurable_const_mul _).prodMap measurable_id
  have hS : Measurable fun y : Idx n → ℝ => fun i => l * y i :=
    measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i)
  rw [cplQ, Measure.map_map measurable_snd (hX.prodMk hY)]
  have e : (Prod.snd ∘ fun q : ℝ × Zn n => (cplX G σ n q, cplY l n q)) =
      (fun y : Idx n → ℝ => fun i => l * y i) ∘ (fun p : ℝ × Zn n => P99bcb804.G n p.1 p.2) ∘
        Prod.map (fun w : ℝ => √((2 : ℝ) ^ n) * w) id := rfl
  rw [e, ← Measure.map_map hS ((measurable_G n).comp hW), ← Measure.map_map (measurable_G n) hW,
    ← Measure.map_prod_map _ _ (measurable_const_mul _) measurable_id, Measure.map_id]
  have hg : (gaussianReal 0 1).map (fun w : ℝ => √((2 : ℝ) ^ n) * w) = gaussianReal 0 (2 ^ n) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 ^ n)]
  rw [hg, (gLaw n).map_eq]
  exact Measure.pi_map_pi (fun _ => (measurable_const_mul l).aemeasurable)

end Kb1

end P99bcb804

end X84_Kb1

section X85_Kb2

/-! R4 / Kb2 (block coupling, deterministic bound): on the on-range event the partial-sum
deviation of the coupling is bounded by the root error plus `C` times the path functional
pieces `n + PZ + PX + (Wx X + Wx Y)/2` along some leaf path (`dev_le`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

section Kb2

variable {G : Measure ℝ} [IsProbabilityMeasure G]

/-- The smoothed node split. -/
noncomputable def fK (G : Measure ℝ) (σ : ℝ) : ℕ → ℝ → ℝ → ℝ :=
  fun n T z0 => qnt (κC G (Idx n) σ T) (Phi z0)

lemma cplX_eq (σ : ℝ) (n : ℕ) (q : ℝ × Zn n) :
    cplX G σ n q = Bld (fK G σ) n (Tq G σ n q.1) q.2 := rfl

lemma cplY_eq {l : ℝ} (hl : l ≠ 0) (n : ℕ) (q : ℝ × Zn n) :
    cplY l n q = Bld (gS l) n (l * (√((2 : ℝ) ^ n) * q.1)) q.2 := by
  rw [Bld_gauss hl]
  funext i
  simp only [cplY]
  congr 2
  field_simp

theorem dev_le {σ l c ε C : ℝ} (hl : l ≠ 0) (hC : 1 ≤ C) {m0 : ℕ}
    (hnode : ∀ m, m0 ≤ m → ∀ S S' z0 : ℝ, |S| ≤ c * 2 ^ (m + 1) →
      |z0| ≤ ε * √((2 : ℝ) ^ (m + 1)) →
      |fK G σ m S z0 - gS l m S' z0| ≤ C * (1 + z0 ^ 2 + S ^ 2 / 2 ^ (m + 1)))
    (n : ℕ) (q : ℝ × Zn n) (hX : OnX m0 c n (cplX G σ n q)) (hZ : OnZ m0 ε n q.2) (k : ℕ) :
    ∃ i, |ps n (cplX G σ n q) k - ps n (cplY l n q) k| ≤
      2 * |Tq G σ n q.1 - l * (√((2 : ℝ) ^ n) * q.1)| +
        2 * C * (n + PZ n q.2 i + PX m0 n (cplX G σ n q) i +
          (Wx m0 n (cplX G σ n q) i + Wx m0 n (cplY l n q) i) / 2) := by
  have hp := pathBc (fK G σ) (gS l) m0 n (Tq G σ n q.1) (l * (√((2 : ℝ) ^ n) * q.1)) q.2 k
  have hOn := OnL_of m0 c ε n _ q.2 hX hZ
  rw [cplX_eq] at hOn
  obtain ⟨i, hi⟩ := DBc_le (fK G σ) (gS l) m0 hC hnode n (Tq G σ n q.1)
    (l * (√((2 : ℝ) ^ n) * q.1)) q.2 hOn
  refine ⟨i, ?_⟩
  have hPQ := PQ_le m0 n (Bld (fK G σ) n (Tq G σ n q.1) q.2)
    (Bld (gS l) n (l * (√((2 : ℝ) ^ n) * q.1)) q.2) q.2 i
  rw [cplX_eq, cplY_eq hl]
  have h1 : C * PQ m0 n (Bld (fK G σ) n (Tq G σ n q.1) q.2)
      (Bld (gS l) n (l * (√((2 : ℝ) ^ n) * q.1)) q.2) q.2 i ≤
      C * (n + PZ n q.2 i + PX m0 n (Bld (fK G σ) n (Tq G σ n q.1) q.2) i +
        (Wx m0 n (Bld (fK G σ) n (Tq G σ n q.1) q.2) i +
          Wx m0 n (Bld (gS l) n (l * (√((2 : ℝ) ^ n) * q.1)) q.2) i) / 2) :=
    mul_le_mul_of_nonneg_left hPQ (by linarith)
  linarith

end Kb2

end P99bcb804

end X85_Kb2

section X86_Kb3

/-! R4 / Kb3 (block tail helpers): `exists_pow_between` (choice of the cutoff `m0` per tail
level), `hnode_mono` (node hypothesis is monotone in the range constant `c`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma exists_pow_between {x : ℝ} (hx : 1 ≤ x) : ∃ m : ℕ, x ≤ 2 ^ m ∧ (2 : ℝ) ^ m ≤ 2 * x := by
  classical
  have hex : ∃ m : ℕ, x ≤ (2 : ℝ) ^ m := by
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hm.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | k
  · simp; linarith
  · have hk : k < Nat.find hex := by omega
    have hlt : ¬ x ≤ (2 : ℝ) ^ k := Nat.find_min hex hk
    rw [not_le] at hlt
    rw [pow_succ]; linarith

section Kb3

variable {G : Measure ℝ} [IsProbabilityMeasure G]

end Kb3

end P99bcb804

end X86_Kb3

section X87_Kb4

/-! R4 / Kb4 (block tail pieces on the base space `μB n = N(0,1) ⊗ γZ n`): marginals of the
coupling (`mpX`, `mpY`), and Markov bounds for each bad piece: root Gaussian, node Gaussians
`PZ`, X-path functional `PX` on `OnX`, cutoff blocks `Wx` on both sides, `¬OnX`, `¬OnZ`. -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

/-- Base space measure of the block coupling. -/
noncomputable def μB (n : ℕ) : Measure (ℝ × Zn n) := (gaussianReal 0 1).prod (γZ n)

instance μB_prob (n : ℕ) : IsProbabilityMeasure (μB n) := by
  haveI := instProbγZ n
  unfold μB; infer_instance

lemma mpW (n : ℕ) : MeasurePreserving (fun q : ℝ × Zn n => q.1) (μB n) (gaussianReal 0 1) := by
  haveI := instProbγZ n
  exact ⟨measurable_fst, by rw [μB, Measure.map_fst_prod]; simp⟩

lemma mpZ (n : ℕ) : MeasurePreserving (fun q : ℝ × Zn n => q.2) (μB n) (γZ n) := by
  haveI := instProbγZ n
  exact ⟨measurable_snd, by rw [μB, Measure.map_snd_prod]; simp⟩

/-- Markov bound with an indicator and a nonnegative extra exponent. -/
lemma markov_on {α : Type} [MeasurableSpace α] (μ : Measure α) {E : Set α} (hE : MeasurableSet E)
    {g r : α → ℝ} (hg : Measurable g) (hr : ∀ a, 0 ≤ r a) {l : ℝ} (hl : 0 < l) (τ : ℝ) :
    μ {a | a ∈ E ∧ τ < g a} ≤
      (∫⁻ a, E.indicator (fun a => ENNReal.ofReal (exp (l * g a + r a))) a ∂μ) *
        ENNReal.ofReal (exp (-(l * τ))) := by
  have hS : MeasurableSet {a | a ∈ E ∧ τ < g a} := hE.inter (measurableSet_lt measurable_const hg)
  rw [← lintegral_indicator_one hS, ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun a => ?_
  by_cases ha : a ∈ E ∧ τ < g a
  · rw [Set.indicator_of_mem (show a ∈ {a | a ∈ E ∧ τ < g a} from ha),
      Set.indicator_of_mem ha.1, Pi.one_apply,
      ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
    have : 0 ≤ l * g a + r a + -(l * τ) := by nlinarith [hr a, ha.2]
    have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal (exp 0) := by simp
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 this)
  · rw [Set.indicator_of_notMem (show a ∉ {a | a ∈ E ∧ τ < g a} from ha)]; exact zero_le'

section Kb4

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma mpX {σ : ℝ} (hσ : σ ≠ 0) (n : ℕ) :
    MeasurePreserving (cplX G σ n) (μB n) (Measure.pi fun _ : Idx n => sL G (Idx 0) σ) := by
  refine ⟨measurable_cplX hσ n, ?_⟩
  have h := cpl_fst (G := G) hσ 1 n
  rw [cplQ, Measure.map_map measurable_fst
    ((measurable_cplX hσ n).prodMk (measurable_cplY 1 n))] at h
  exact h

lemma mpY {σ : ℝ} (hσ : σ ≠ 0) (l : ℝ) (n : ℕ) :
    MeasurePreserving (cplY l n) (μB n)
      (Measure.pi fun _ : Idx n => (gaussianReal 0 1).map (fun y => l * y)) := by
  refine ⟨measurable_cplY l n, ?_⟩
  have h := cpl_snd (G := gaussianReal 0 1) hσ l n
  rw [cplQ, Measure.map_map measurable_snd
    ((measurable_cplX (G := gaussianReal 0 1) hσ n).prodMk (measurable_cplY l n))] at h
  exact h

/-- Root Gaussian piece. -/
lemma pc_w (n : ℕ) (τ : ℝ) :
    μB n {q | τ < q.1 ^ 2} ≤ 2 * ENNReal.ofReal (exp (-(1 / 4 * τ))) := by
  have e : {q : ℝ × Zn n | τ < q.1 ^ 2} = (fun q : ℝ × Zn n => q.1) ⁻¹' {w : ℝ | τ < w ^ 2} := rfl
  rw [e, (mpW n).measure_preimage
    (measurableSet_lt measurable_const (by fun_prop)).nullMeasurableSet]
  exact gauss_tail τ

/-- Node Gaussian path piece. -/
lemma pc_Z (n : ℕ) (i : Idx n) (τ : ℝ) :
    μB n {q | τ < PZ n q.2 i} ≤ 2 ^ n * ENNReal.ofReal (exp (-(1 / 4 * τ))) := by
  haveI := instProbγZ n
  have e : {q : ℝ × Zn n | τ < PZ n q.2 i} = (fun q : ℝ × Zn n => q.2) ⁻¹' {z | τ < PZ n z i} := rfl
  rw [e, (mpZ n).measure_preimage
    (measurableSet_lt measurable_const (measurable_PZ n i)).nullMeasurableSet]
  refine markov_exp (γZ n) (measurable_PZ n i) (by norm_num) ?_ τ
  refine le_trans (le_of_eq ?_) (momZ n i)
  congr 1; funext z; congr 2; ring

lemma pc_notOnZ (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) (m0 : ℕ) :
    μB n {q | ¬ OnZ m0 ε n q.2} ≤
      ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(1 / 4 * (ε ^ 2 * 2 ^ m0))))) := by
  have e : {q : ℝ × Zn n | ¬ OnZ m0 ε n q.2} = (fun q : ℝ × Zn n => q.2) ⁻¹' {z | ¬ OnZ m0 ε n z} :=
    rfl
  rw [e, (mpZ n).measure_preimage (s := {z | ¬ OnZ m0 ε n z})
    (measurableSet_OnZ m0 ε n).compl.nullMeasurableSet]
  exact notOnZ hε m0 n

lemma tpq_nonneg (m0 d : ℕ) (x : Idx d → ℝ) : 0 ≤ tpq m0 d x := by
  unfold tpq; split_ifs
  · positivity
  · exact le_refl _

lemma Wx_eq_sum {m0 : ℕ} : ∀ {n : ℕ}, n ≤ m0 → ∀ (x : Idx n → ℝ) (i : Idx n),
    Wx m0 n x i = ∑ j, |x j|
  | 0, _, _, _ => rfl
  | n + 1, h, x, i => by
      show (if n + 1 ≤ m0 then ∑ j, |x j| else _) = _
      rw [if_pos h]

/-- Gaussian side absolute moment of `N(0,1).map (l·)`. -/
lemma absmom_gl {l a : ℝ} (hl : 0 ≤ l) :
    ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂((gaussianReal 0 1).map (fun y => l * y)) ≤
      2 * ENNReal.ofReal (exp ((a * l) ^ 2 / 2)) := by
  rw [lintegral_map (by fun_prop) (measurable_const_mul l)]
  have e : (fun y : ℝ => ENNReal.ofReal (exp (a * |l * y|))) =
      fun y => ENNReal.ofReal (exp ((a * l) * |y|)) := by
    funext y; rw [abs_mul, abs_of_nonneg hl]; ring_nf
  rw [e]
  refine (absmom_gauss 1 (a * l)).trans (le_of_eq ?_)
  simp

end Kb4

lemma one_le_two_mul_exp {r : ℝ} (hr : 0 ≤ r) : (1 : ℝ≥0∞) ≤ 2 * ENNReal.ofReal (exp r) := by
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (exp r) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hr)
  calc (1 : ℝ≥0∞) ≤ ENNReal.ofReal (exp r) := h1
    _ ≤ 2 * ENNReal.ofReal (exp r) := le_mul_of_one_le_left zero_le' (by norm_num)

lemma pc_WY (n m0 : ℕ) {σ : ℝ} (hσ : σ ≠ 0) {l : ℝ} (hl : 0 ≤ l) {a : ℝ} (ha : 0 < a)
    (i : Idx n) (τ : ℝ) :
    μB n {q | τ < Wx m0 n (cplY l n q) i} ≤
      (2 * ENNReal.ofReal (exp ((a * l) ^ 2 / 2))) ^ (2 ^ m0) * ENNReal.ofReal (exp (-(a * τ))) := by
  haveI : IsProbabilityMeasure ((gaussianReal 0 1).map (fun y : ℝ => l * y)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul l).aemeasurable
  have e : {q : ℝ × Zn n | τ < Wx m0 n (cplY l n q) i} =
      (cplY l n) ⁻¹' {x | τ < Wx m0 n x i} := rfl
  rw [e, (mpY hσ l n).measure_preimage
    (measurableSet_lt measurable_const (measurable_Wx m0 n i)).nullMeasurableSet]
  exact markov_exp _ (measurable_Wx m0 n i) ha
    (momW _ m0 (one_le_two_mul_exp (by positivity)) (absmom_gl hl) n i) τ

section Kb4X

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma pc_notOnX (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 6 * min t1 (1 / (B + 1))) {σ : ℝ} (hσ : σ ≠ 0) (hσ1 : |σ| ≤ 1)
    (m0 n : ℕ) :
    μB n {q | ¬ OnX m0 c n (cplX G σ n q)} ≤
      ENNReal.ofReal ((2 ^ n - 1) * (2 * exp (-(c ^ 2 * 2 ^ m0 / 12)))) := by
  have e : {q : ℝ × Zn n | ¬ OnX m0 c n (cplX G σ n q)} =
      (cplX G σ n) ⁻¹' {x | ¬ OnX m0 c n x} := rfl
  rw [e, (mpX hσ n).measure_preimage (s := {x | ¬ OnX m0 c n x})
    (measurableSet_OnX m0 c n).compl.nullMeasurableSet]
  exact notOnX ha0 hexp hm ht1 h2 hB hV hW hc0 hc hσ1 m0 n

lemma pc_PX (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {c : ℝ} (hc : c ≤ 6 * min t1 (1 / (B + 1))) {σ : ℝ} (hσ : σ ≠ 0) (hσ1 : |σ| ≤ 1)
    (m0 n : ℕ) (i : Idx n) (τ : ℝ) :
    μB n {q | OnX m0 c n (cplX G σ n q) ∧ τ < PX m0 n (cplX G σ n q) i} ≤
      ENNReal.ofReal (Amom ^ n) * ENNReal.ofReal (exp (-(1 / 144 * τ))) := by
  have e : {q : ℝ × Zn n | OnX m0 c n (cplX G σ n q) ∧ τ < PX m0 n (cplX G σ n q) i} =
      (cplX G σ n) ⁻¹' {x | x ∈ {x | OnX m0 c n x} ∧ τ < PX m0 n x i} := rfl
  rw [e, (mpX hσ n).measure_preimage (s := {x | x ∈ {x | OnX m0 c n x} ∧ τ < PX m0 n x i})
    ((measurableSet_OnX m0 c n).inter
      (measurableSet_lt measurable_const (measurable_PX m0 n i))).nullMeasurableSet]
  refine (markov_on _ (measurableSet_OnX m0 c n) (measurable_PX m0 n i)
    (r := fun x => 3 * (1 / 144) * tpq m0 n x)
    (fun x => by have := tpq_nonneg m0 n x; positivity) (by norm_num : (0 : ℝ) < 1 / 144) τ).trans ?_
  gcongr
  exact momPX _ m0 (by norm_num) one_le_Amom
    (fun d => mom_on ha0 hexp hm ht1 h2 hB hV hW hc hσ1 d (by norm_num) (by norm_num)) n i

lemma pc_WX (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    {σ : ℝ} (hσ : σ ≠ 0) (hσ1 : |σ| ≤ 1) {a : ℝ} (ha : 0 < a) (hat : a ≤ min t1 (1 / (B + 1)))
    (m0 n : ℕ) (i : Idx n) (τ : ℝ) :
    μB n {q | τ < Wx m0 n (cplX G σ n q) i} ≤
      (2 * ENNReal.ofReal (exp (3 * a ^ 2))) ^ (2 ^ m0) * ENNReal.ofReal (exp (-(a * τ))) := by
  have e : {q : ℝ × Zn n | τ < Wx m0 n (cplX G σ n q) i} =
      (cplX G σ n) ⁻¹' {x | τ < Wx m0 n x i} := rfl
  rw [e, (mpX hσ n).measure_preimage
    (measurableSet_lt measurable_const (measurable_Wx m0 n i)).nullMeasurableSet]
  exact markov_exp _ (measurable_Wx m0 n i) ha
    (momW _ m0 (one_le_two_mul_exp (by positivity))
      (absmom_nu ha0 hexp hm ht1 h2 hB hV hW hσ1 (by rw [abs_of_pos ha]; exact hat)) n i) τ

end Kb4X

end P99bcb804

end X87_Kb4

section X88_Kb5

/-! R4 / Kb5 (block tail, deterministic inclusions + union bound): `dev_big` (cutoff below `n`:
the deviation event lies in the bad sets), `dev_small` (cutoff above `n`: crude `Wx` bound),
`union4`, `union_bd` (finite union bound with real bounds). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma union4 {α : Type} [MeasurableSpace α] (μ : Measure α) {A B C D : Set α} {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hA : μ A ≤ ENNReal.ofReal a) (hB : μ B ≤ ENNReal.ofReal b) (hC : μ C ≤ ENNReal.ofReal c)
    (hD : μ D ≤ ENNReal.ofReal d) :
    μ (A ∪ B ∪ C ∪ D) ≤ ENNReal.ofReal (a + b + c + d) := by
  calc μ (A ∪ B ∪ C ∪ D) ≤ μ (A ∪ B ∪ C) + μ D := measure_union_le _ _
    _ ≤ μ (A ∪ B) + μ C + μ D := by gcongr; exact measure_union_le _ _
    _ ≤ μ A + μ B + μ C + μ D := by gcongr; exact measure_union_le _ _
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c + ENNReal.ofReal d := by
        gcongr
    _ = ENNReal.ofReal (a + b + c + d) := by
        rw [ENNReal.ofReal_add (by positivity) hd, ENNReal.ofReal_add (by positivity) hc,
          ENNReal.ofReal_add ha hb]

lemma union_bd {α ι : Type} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    {S1 S2 S3 S4 : Set α} {T5 T6 T7 T8 : ι → Set α} {b1 b2 b3 b4 b5 b6 b7 b8 : ℝ}
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) (hb4 : 0 ≤ b4) (hb5 : 0 ≤ b5) (hb6 : 0 ≤ b6)
    (hb7 : 0 ≤ b7) (hb8 : 0 ≤ b8)
    (h1 : μ S1 ≤ ENNReal.ofReal b1) (h2 : μ S2 ≤ ENNReal.ofReal b2) (h3 : μ S3 ≤ ENNReal.ofReal b3)
    (h4 : μ S4 ≤ ENNReal.ofReal b4) (h5 : ∀ i, μ (T5 i) ≤ ENNReal.ofReal b5)
    (h6 : ∀ i, μ (T6 i) ≤ ENNReal.ofReal b6) (h7 : ∀ i, μ (T7 i) ≤ ENNReal.ofReal b7)
    (h8 : ∀ i, μ (T8 i) ≤ ENNReal.ofReal b8) :
    μ (S1 ∪ S2 ∪ S3 ∪ S4 ∪ ⋃ i, (T5 i ∪ T6 i ∪ T7 i ∪ T8 i)) ≤
      ENNReal.ofReal (b1 + b2 + b3 + b4 + Fintype.card ι * (b5 + b6 + b7 + b8)) := by
  have hU : μ (⋃ i, (T5 i ∪ T6 i ∪ T7 i ∪ T8 i)) ≤
      ENNReal.ofReal (Fintype.card ι * (b5 + b6 + b7 + b8)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    calc ∑ i, μ (T5 i ∪ T6 i ∪ T7 i ∪ T8 i) ≤ ∑ _i : ι, ENNReal.ofReal (b5 + b6 + b7 + b8) :=
          Finset.sum_le_sum fun i _ => union4 μ hb5 hb6 hb7 hb8 (h5 i) (h6 i) (h7 i) (h8 i)
      _ = ENNReal.ofReal (Fintype.card ι * (b5 + b6 + b7 + b8)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  refine (measure_union_le _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add (union4 μ hb1 hb2 hb3 hb4 h1 h2 h3 h4) hU

section Kb5

variable {G : Measure ℝ} [IsProbabilityMeasure G]

theorem dev_big {σ l c ε Cn C2 τ Cu ε' : ℝ} (hl : l ≠ 0) (hCn : 1 ≤ Cn) {m0 : ℕ}
    (hnode : ∀ m, m0 ≤ m → ∀ S S' z0 : ℝ, |S| ≤ c * 2 ^ (m + 1) →
      |z0| ≤ ε * √((2 : ℝ) ^ (m + 1)) →
      |fK G σ m S z0 - gS l m S' z0| ≤ Cn * (1 + z0 ^ 2 + S ^ 2 / 2 ^ (m + 1)))
    (n : ℕ) (hC2 : 0 ≤ C2)
    (hroot : ∀ w : ℝ, w ^ 2 ≤ ε' → |Tq G σ n w - l * (√((2 : ℝ) ^ n) * w)| ≤ C2 * (1 + w ^ 2))
    (hCu : 2 * C2 * (1 + τ) + 2 * Cn * (n + 3 * τ) ≤ Cu) :
    {q : ℝ × Zn n | ∃ k : ℕ, Cu < |ps n (cplX G σ n q) k - ps n (cplY l n q) k|} ⊆
      {q | ε' < q.1 ^ 2} ∪ {q | ¬ OnX m0 c n (cplX G σ n q)} ∪ {q | ¬ OnZ m0 ε n q.2} ∪
        {q | τ < q.1 ^ 2} ∪
        ⋃ i, ({q | τ < PZ n q.2 i} ∪
          {q | OnX m0 c n (cplX G σ n q) ∧ τ < PX m0 n (cplX G σ n q) i} ∪
          {q | τ < Wx m0 n (cplX G σ n q) i} ∪ {q | τ < Wx m0 n (cplY l n q) i}) := by
  intro q hq0
  obtain ⟨k, hk⟩ := hq0
  by_contra hq
  have h1 : q.1 ^ 2 ≤ ε' := by
    by_contra h; exact hq (Or.inl (Or.inl (Or.inl (Or.inl (lt_of_not_ge h)))))
  have hX : OnX m0 c n (cplX G σ n q) := by
    by_contra h; exact hq (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hZ : OnZ m0 ε n q.2 := by
    by_contra h; exact hq (Or.inl (Or.inl (Or.inr h)))
  have hw : q.1 ^ 2 ≤ τ := by
    by_contra h; exact hq (Or.inl (Or.inr (lt_of_not_ge h)))
  have hT : ∀ i, PZ n q.2 i ≤ τ ∧ PX m0 n (cplX G σ n q) i ≤ τ ∧
      Wx m0 n (cplX G σ n q) i ≤ τ ∧ Wx m0 n (cplY l n q) i ≤ τ := by
    intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_contra h
      exact hq (Or.inr (mem_iUnion.2 ⟨i, Or.inl (Or.inl (Or.inl (lt_of_not_ge h)))⟩))
    · by_contra h
      exact hq (Or.inr (mem_iUnion.2 ⟨i, Or.inl (Or.inl (Or.inr ⟨hX, lt_of_not_ge h⟩))⟩))
    · by_contra h
      exact hq (Or.inr (mem_iUnion.2 ⟨i, Or.inl (Or.inr (lt_of_not_ge h))⟩))
    · by_contra h
      exact hq (Or.inr (mem_iUnion.2 ⟨i, Or.inr (lt_of_not_ge h)⟩))
  obtain ⟨i, hi⟩ := dev_le hl hCn hnode n q hX hZ k
  obtain ⟨hPZ, hPX, hWX, hWY⟩ := hT i
  have hr := hroot q.1 h1
  have hr2 : 2 * |Tq G σ n q.1 - l * (√((2 : ℝ) ^ n) * q.1)| ≤ 2 * C2 * (1 + τ) := by
    have : C2 * (1 + q.1 ^ 2) ≤ C2 * (1 + τ) := mul_le_mul_of_nonneg_left (by linarith) hC2
    linarith
  have hp2 : 2 * Cn * (n + PZ n q.2 i + PX m0 n (cplX G σ n q) i +
      (Wx m0 n (cplX G σ n q) i + Wx m0 n (cplY l n q) i) / 2) ≤ 2 * Cn * (n + 3 * τ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

theorem dev_small {σ l τ Cu : ℝ} {m0 n : ℕ} (hn : n ≤ m0) (i0 : Idx n) (hCu : 2 * τ ≤ Cu) :
    {q : ℝ × Zn n | ∃ k : ℕ, Cu < |ps n (cplX G σ n q) k - ps n (cplY l n q) k|} ⊆
      {q | τ < Wx m0 n (cplX G σ n q) i0} ∪ {q | τ < Wx m0 n (cplY l n q) i0} := by
  intro q hq0
  obtain ⟨k, hk⟩ := hq0
  by_contra hq
  have hX : Wx m0 n (cplX G σ n q) i0 ≤ τ := by
    by_contra h; exact hq (Or.inl (lt_of_not_ge h))
  have hY : Wx m0 n (cplY l n q) i0 ≤ τ := by
    by_contra h; exact hq (Or.inr (lt_of_not_ge h))
  rw [Wx_eq_sum hn] at hX hY
  have a1 := abs_ps_le n (cplX G σ n q) k
  have a2 := abs_ps_le n (cplY l n q) k
  have a3 := abs_sub (ps n (cplX G σ n q) k) (ps n (cplY l n q) k)
  linarith

end Kb5

end P99bcb804

end X88_Kb5

section X89_Kb6

/-! R4 / Kb6 (block tail, real arithmetic): `wx_real` (cutoff-block moment against the tail
level), `exp_tail_le` (Gaussian/Chernoff pieces), `pow_two_mul_ofReal` (ENNReal shape). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma wx_real {LE K1 a u N' : ℝ} {m0 : ℕ} (hLE : 0 ≤ LE) (ha : 0 < a)
    (hm0 : (2 : ℝ) ^ m0 ≤ 2 * (K1 * u + N')) (hu : 0 ≤ u) :
    exp LE ^ (2 ^ m0) * exp (-(a * ((144 + (2 * LE * K1 + 1) / a) * u))) ≤
      exp (2 * LE * N') * exp (-u) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have e : a * ((144 + (2 * LE * K1 + 1) / a) * u) = 144 * a * u + (2 * LE * K1 + 1) * u := by
    field_simp
  rw [e]
  push_cast
  have h1 := mul_le_mul_of_nonneg_right hm0 hLE
  have h2 : 0 ≤ 144 * a * u := by positivity
  linarith

lemma pow_two_mul_ofReal {y z : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    (2 * ENNReal.ofReal y) ^ k * ENNReal.ofReal z = ENNReal.ofReal ((2 * y) ^ k * z) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

lemma two_mul_ofReal (y : ℝ) : 2 * ENNReal.ofReal y = ENNReal.ofReal (2 * y) := by
  rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

lemma exp_neg_le_of {p q : ℝ} (h : p ≤ q) : exp (-q) ≤ exp (-p) :=
  Real.exp_le_exp.2 (neg_le_neg h)

/-- `(2^n - 1)·2e^{-κ 2^m0} ≤ 2^n·2e^{-u}` when `u ≤ κ 2^m0`. -/
lemma notOn_real {κ u : ℝ} {n m0 : ℕ} (h : u ≤ κ * 2 ^ m0) :
    ((2 : ℝ) ^ n - 1) * (2 * exp (-(κ * 2 ^ m0))) ≤ 2 ^ n * (2 * exp (-u)) := by
  have h1 : (2 : ℝ) ^ n - 1 ≤ 2 ^ n := by linarith
  have h0 : (0 : ℝ) ≤ 2 ^ n - 1 := by
    have := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 2); linarith
  have h2 := exp_neg_le_of h
  calc ((2 : ℝ) ^ n - 1) * (2 * exp (-(κ * 2 ^ m0))) ≤ (2 ^ n - 1) * (2 * exp (-u)) := by
        gcongr
    _ ≤ 2 ^ n * (2 * exp (-u)) := by gcongr

end P99bcb804

end X89_Kb6

section X90_Kb7

/-! R4 / Kb7 (block tail for the smoothed block coupling): `block_tail`:
`cplQ G σ l n {∃ k, C (n+1+s) < |ps X k - ps Y k|} ≤ A R^n e^{-s}` for `0 < σ ≤ 1`,
`σ⁻¹ ≤ e^n`, `l = √(L2s G σ 0)`; the cutoff `m0` is chosen per tail level (`exists_pow_between`). -/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace P99bcb804

lemma measurableSet_devQ (n : ℕ) (c : ℝ) :
    MeasurableSet {p : (Idx n → ℝ) × (Idx n → ℝ) | ∃ k : ℕ, c < |ps n p.1 k - ps n p.2 k|} := by
  have : {p : (Idx n → ℝ) × (Idx n → ℝ) | ∃ k : ℕ, c < |ps n p.1 k - ps n p.2 k|} =
      ⋃ k : ℕ, {p | c < |ps n p.1 k - ps n p.2 k|} := by ext p; simp
  rw [this]
  exact MeasurableSet.iUnion fun k => measurableSet_lt measurable_const
    ((((measurable_ps n k).comp measurable_fst).sub ((measurable_ps n k).comp measurable_snd)).abs)

/-- Final real inequality of the union bound. -/
lemma total_real {X Y A0 E Es : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hA0 : 0 ≤ A0) (hE : 0 ≤ E)
    (hEs : E ≤ Es) :
    2 * E + X * (2 * E) + X * (2 * E) + 2 * E + X * (X * E + Y * E + A0 * E + A0 * E) ≤
      (10 + 2 * A0) * (X * X * Y) * Es := by
  have hX0 : (0 : ℝ) ≤ X := by linarith only [hX]
  have hXY := mul_le_mul hX hY zero_le_one hX0
  have h1 : X ≤ X * X * Y := by
    have h' := mul_le_mul_of_nonneg_left hXY hX0; linarith only [h']
  have h2 : X * X ≤ X * X * Y := by
    have h' := mul_le_mul_of_nonneg_left hY (mul_nonneg hX0 hX0); linarith only [h']
  have h3 : X * Y ≤ X * X * Y := by
    have h' := mul_le_mul_of_nonneg_right hX (mul_nonneg hX0 (by linarith only [hY] : (0:ℝ) ≤ Y))
    linarith only [h']
  have h4 : 1 ≤ X * X * Y := by linarith
  have hP : 4 + 4 * X + X * X + X * Y + 2 * A0 * X ≤ (10 + 2 * A0) * (X * X * Y) := by
    linarith [mul_le_mul_of_nonneg_left h1 hA0]
  have hPos : 0 ≤ (10 + 2 * A0) * (X * X * Y) := mul_nonneg (by linarith only [hA0]) (by linarith only [h4])
  calc 2 * E + X * (2 * E) + X * (2 * E) + 2 * E + X * (X * E + Y * E + A0 * E + A0 * E)
        = (4 + 4 * X + X * X + X * Y + 2 * A0 * X) * E := by ring
    _ ≤ (10 + 2 * A0) * (X * X * Y) * E := mul_le_mul_of_nonneg_right hP hE
    _ ≤ (10 + 2 * A0) * (X * X * Y) * Es := mul_le_mul_of_nonneg_left hEs hPos

section Kb7

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

set_option maxHeartbeats 1000000 in
theorem block_tail (ha0 : 0 < a0)
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
    ∃ C A R : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ R ∧
      ∀ (n : ℕ) (σ : ℝ), 0 < σ → σ ≤ 1 → σ⁻¹ ≤ exp (2 * (n + 1)) → ∀ s : ℝ, 0 ≤ s →
        cplQ G σ (√(L2s G σ 0)) n
            {p | ∃ k : ℕ, C * (n + 1 + s) < |ps n p.1 k - ps n p.2 k|} ≤
          ENNReal.ofReal (A * R ^ n * exp (-s)) := by
  obtain ⟨C1, εq, β1, N3, hC1, hεq, hβ1, hN3, H⟩ :=
    node_κ ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  obtain ⟨C2, εr, β2, N2, hC2, hεr, hβ2, Hr⟩ :=
    root_qnt ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  clear hG hp0 hp1 hv0
  have htb : 0 < min t1 (1 / (B + 1)) := lt_min ht1 (by positivity)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (t1 / 4) (6 * min t1 (1 / (B + 1))) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact lt_min (by linarith only [ht1]) (by linarith only [htb])
  have hc1 : c ≤ t1 / 4 := by rw [hc]; exact min_le_left _ _
  have hc2 : c ≤ 6 * min t1 (1 / (B + 1)) := by rw [hc]; exact min_le_right _ _
  clear hc
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = min t1 (1 / (B + 1)) := ⟨_, rfl⟩
  have ha0' : 0 < a := ha ▸ htb
  obtain ⟨LE, hLE⟩ : ∃ LE : ℝ, LE = Real.log 2 + 3 * a ^ 2 := ⟨_, rfl⟩
  have hLE0 : 0 ≤ LE := by
    rw [hLE]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hexpLE : exp LE = 2 * exp (3 * a ^ 2) := by
    rw [hLE, Real.exp_add, Real.exp_log (by norm_num)]
  obtain ⟨Cn, hCn⟩ : ∃ Cn : ℝ, Cn = max (3 * C1) 1 := ⟨_, rfl⟩
  have hCn1 : 1 ≤ Cn := hCn ▸ le_max_right _ _
  have hCn3 : 3 * C1 ≤ Cn := hCn ▸ le_max_left _ _
  have hε : 0 < εq / 4 := by positivity
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ,
      K1 = 1 + 2 / β1 + 2 / β2 + 12 / c ^ 2 + 4 / (εq / 4) ^ 2 + 8 / εr ^ 2 := ⟨_, rfl⟩
  have n1 : 0 ≤ 2 / β1 := by positivity
  have n2 : 0 ≤ 2 / β2 := by positivity
  have n3 : 0 ≤ 12 / c ^ 2 := by positivity
  have n4 : 0 ≤ 4 / (εq / 4) ^ 2 := by positivity
  have n5 : 0 ≤ 8 / εr ^ 2 := by positivity
  have hK1_1 : 1 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
  have hK1_0 : 0 ≤ K1 := by linarith only [hK1_1]
  have hK1_b1 : 2 ≤ β1 * K1 := by
    have : 2 / β1 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
    calc (2 : ℝ) = β1 * (2 / β1) := by field_simp
      _ ≤ β1 * K1 := mul_le_mul_of_nonneg_left this hβ1.le
  have hK1_b2 : 2 ≤ β2 * K1 := by
    have : 2 / β2 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
    calc (2 : ℝ) = β2 * (2 / β2) := by field_simp
      _ ≤ β2 * K1 := mul_le_mul_of_nonneg_left this hβ2.le
  have hK1_c : 12 ≤ c ^ 2 * K1 := by
    have : 12 / c ^ 2 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
    calc (12 : ℝ) = c ^ 2 * (12 / c ^ 2) := by field_simp
      _ ≤ c ^ 2 * K1 := mul_le_mul_of_nonneg_left this (sq_nonneg c)
  have hK1_e : 4 ≤ (εq / 4) ^ 2 * K1 := by
    have : 4 / (εq / 4) ^ 2 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
    calc (4 : ℝ) = (εq / 4) ^ 2 * (4 / (εq / 4) ^ 2) := by field_simp
      _ ≤ (εq / 4) ^ 2 * K1 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hK1_r : 8 ≤ εr ^ 2 * K1 := by
    have : 8 / εr ^ 2 ≤ K1 := by rw [hK1]; linarith only [n1, n2, n3, n4, n5]
    calc (8 : ℝ) = εr ^ 2 * (8 / εr ^ 2) := by field_simp
      _ ≤ εr ^ 2 * K1 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
  clear n1 n2 n3 n4 n5 hK1
  have hpack : (c ≤ t1 / 4 ∧ c ≤ 6 * min t1 (1 / (B + 1))) ∧ (0 < εq / 4 ∧ 4 ≤ (εq / 4) ^ 2 * K1) :=
    ⟨⟨hc1, hc2⟩, hε, hK1_e⟩
  clear hc1 hc2 hε hK1_e
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, K2 = 144 + (2 * LE * K1 + 1) / a := ⟨_, rfl⟩
  have hK2_144 : 144 ≤ K2 := by
    rw [hK2]; have : 0 ≤ (2 * LE * K1 + 1) / a := by positivity
    linarith only [this]
  have hK2_0 : 0 ≤ K2 := by linarith only [hK2_144]
  obtain ⟨A0, hA0⟩ : ∃ A0 : ℝ, A0 = exp (2 * LE * (|N2| + N3)) := ⟨_, rfl⟩
  have hA0p : 0 < A0 := hA0 ▸ exp_pos _
  have hCnn : 0 ≤ Cn := by linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * C2 + 2 * C2 * K2 + 2 * Cn + 6 * Cn * K2 + 2 * K2 := ⟨_, rfl⟩
  have hP : 0 ≤ 2 * C2 + 2 * C2 * K2 + 2 * Cn + 6 * Cn * K2 := by
    have q1 := mul_nonneg hC2.le hK2_0
    have q2 := mul_nonneg hCnn hK2_0
    linarith only [q1, q2, hC2, hCnn]
  have hCpos : 0 < C := by rw [hC]; linarith only [hP, hK2_144]
  have hR1 : 1 ≤ 4 * Amom := by have := one_le_Amom; linarith only [this]
  refine ⟨C, 10 + 2 * A0, 4 * Amom, hCpos, by linarith only [hA0p], hR1, ?_⟩
  intro n σ hσ0 hσ1 hσn s hs
  haveI : Fact (σ ≠ 0) := ⟨hσ0.ne'⟩
  have hσabs : |σ| ≤ 1 := abs_le.2 ⟨by linarith only [hσ0], hσ1⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = n + 1 + s := ⟨_, rfl⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hu1 : 1 ≤ u := by rw [hu]; linarith only [hn0, hs]
  have hu0 : 0 ≤ u := by linarith only [hu1]
  have hnu : (n : ℝ) ≤ u := by rw [hu]; linarith only [hn0, hs]
  have hnu1 : (n : ℝ) + 1 ≤ u := by rw [hu]; linarith only [hn0, hs]
  have hsu : s ≤ u := by rw [hu]; linarith only [hn0, hs]
  rw [show (n : ℝ) + 1 + s = u from hu.symm]
  have hK1u : 0 ≤ K1 * u := mul_nonneg hK1_0 hu0
  have hx1 : 1 ≤ K1 * u + |N2| + N3 := by have := abs_nonneg N2; linarith only [this, hK1u, hN3]
  obtain ⟨m0, hm0a, hm0b⟩ := exists_pow_between hx1
  have hL := L2s_bd (G := G) hV hσ0 hσ1 (t := 0) (by simp; exact ht1.le)
  set l := √(L2s G σ 0) with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 (by linarith)
  have hl2 : l ^ 2 ≤ 3 := by rw [hl, Real.sq_sqrt (by linarith)]; exact hL.2
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = K2 * u := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτ]; exact mul_nonneg hK2_0 hu0
  have hτu : 144 * u ≤ τ := by rw [hτ]; exact mul_le_mul_of_nonneg_right hK2_144 hu0
  -- the cutoff-block moments
  have hcore : exp LE ^ (2 ^ m0) * exp (-(a * τ)) ≤ A0 * exp (-u) := by
    rw [hτ, hK2, hA0]
    exact wx_real hLE0 ha0' (by linarith) hu0
  clear hK2 hA0
  have hWXr : ∀ i : Idx n, μB n {q | τ < Wx m0 n (cplX G σ n q) i} ≤
      ENNReal.ofReal (A0 * exp (-u)) := by
    intro i
    refine (pc_WX ha0 hexp hm ht1 h2 hB hV hW hσ0.ne' hσabs ha0' (le_of_eq ha) m0 n i τ).trans ?_
    rw [pow_two_mul_ofReal (exp_pos _).le, ← hexpLE]
    exact ENNReal.ofReal_le_ofReal hcore
  clear ha
  have hWYr : ∀ i : Idx n, μB n {q | τ < Wx m0 n (cplY l n q) i} ≤
      ENNReal.ofReal (A0 * exp (-u)) := by
    intro i
    refine (pc_WY n m0 hσ0.ne' hl0.le ha0' i τ).trans ?_
    rw [pow_two_mul_ofReal (exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    refine le_trans ?_ hcore
    gcongr
    rw [hexpLE]
    gcongr
    have e2 : (a * l) ^ 2 = a ^ 2 * l ^ 2 := by ring
    linarith [mul_le_mul_of_nonneg_left hl2 (sq_nonneg a), sq_nonneg a]
  have hmeasQ : Measurable fun q : ℝ × Zn n => (cplX G σ n q, cplY l n q) :=
    (measurable_cplX hσ0.ne' n).prodMk (measurable_cplY l n)
  have e : cplQ G σ l n {p | ∃ k : ℕ, C * u < |ps n p.1 k - ps n p.2 k|} =
      μB n {q | ∃ k : ℕ, C * u < |ps n (cplX G σ n q) k - ps n (cplY l n q) k|} := by
    rw [cplQ, Measure.map_apply hmeasQ (measurableSet_devQ n _)]; rfl
  rw [e]
  clear e
  have hEs : exp (-u) ≤ exp (-s) := exp_neg_le_of hsu
  have hRn : (1 : ℝ) ≤ (4 * Amom) ^ n := one_le_pow₀ hR1
  rcases le_or_gt n m0 with hn | hn
  · -- cutoff above the block: crude bound
    have i0 : Idx n := Classical.arbitrary _
    have hCu : 2 * τ ≤ C * u := by
      rw [hC, hτ]; linarith [mul_nonneg hP hu0]
    refine (measure_mono (dev_small (G := G) (σ := σ) (l := l) hn i0 hCu)).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (hWXr i0) (hWYr i0)).trans ?_
    rw [← ENNReal.ofReal_add (mul_nonneg hA0p.le (exp_pos _).le) (mul_nonneg hA0p.le (exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : A0 * exp (-u) ≤ A0 * exp (-s) := mul_le_mul_of_nonneg_left hEs hA0p.le
    have h3 : 0 ≤ exp (-s) := (exp_pos _).le
    have h4 : (10 + 2 * A0) * 1 * exp (-s) ≤ (10 + 2 * A0) * (4 * Amom) ^ n * exp (-s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hRn (by linarith : (0 : ℝ) ≤ 10 + 2 * A0)) h3
    have h5 : (10 + 2 * A0) * 1 * exp (-s) = 10 * exp (-s) + 2 * (A0 * exp (-s)) := by ring
    linarith
  · -- cutoff below the block
    have hpow : (2 : ℝ) ^ m0 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn.le
    have hx2n : K1 * u + |N2| + N3 ≤ 2 ^ n := hm0a.trans hpow
    have hN3m : N3 ≤ (2 : ℝ) ^ m0 := by have := abs_nonneg N2; linarith only [this, hK1u, hm0a]
    have hβ1m : σ⁻¹ ≤ exp (β1 * (2 : ℝ) ^ m0) := by
      refine hσn.trans (Real.exp_le_exp.2 ?_)
      have h1 := mul_le_mul_of_nonneg_right hK1_b1 hu0
      have h2' := mul_le_mul_of_nonneg_left hm0a hβ1.le
      have h3 : 0 ≤ β1 * (|N2| + N3) := mul_nonneg hβ1.le (by have := abs_nonneg N2; linarith only [this, hN3])
      linarith only [h1, h2', h3, hnu1]
    have hnode0 := node_hyp (G := G) hC1 hεq hβ1 H hσ0 hσ1 hL hN3m hβ1m
    have hnode : ∀ m', m0 ≤ m' → ∀ S S' z0 : ℝ, |S| ≤ c * 2 ^ (m' + 1) →
        |z0| ≤ εq / 4 * √((2 : ℝ) ^ (m' + 1)) →
        |fK G σ m' S z0 - gS l m' S' z0| ≤ Cn * (1 + z0 ^ 2 + S ^ 2 / 2 ^ (m' + 1)) := by
      intro m' hm' S S' z0 hS hz
      exact (hnode0 m' hm' S S' z0 (hS.trans (mul_le_mul_of_nonneg_right hpack.1.1 (by positivity)))
        hz).trans (mul_le_mul_of_nonneg_right hCn3 (by positivity))
    have hcard : (Fintype.card (Idx n) : ℝ) = 2 ^ n := by rw [card_Idx]; push_cast; ring
    have hN : (0 : ℝ) < 2 ^ n := by positivity
    have hroot : ∀ w : ℝ, w ^ 2 ≤ εr ^ 2 * 2 ^ n / 2 →
        |Tq G σ n w - l * (√((2 : ℝ) ^ n) * w)| ≤ C2 * (1 + w ^ 2) := by
      intro w hw
      have hN2 : N2 ≤ (Fintype.card (Idx n) : ℝ) := by
        rw [hcard]; have := le_abs_self N2; linarith only [this, hx2n, hK1u, hN3]
      have hβ2n : σ⁻¹ ≤ exp (β2 * Fintype.card (Idx n)) := by
        rw [hcard]
        refine hσn.trans (Real.exp_le_exp.2 ?_)
        have h1 := mul_le_mul_of_nonneg_right hK1_b2 hu0
        have h2' := mul_le_mul_of_nonneg_left hx2n hβ2.le
        have h3 : 0 ≤ β2 * (|N2| + N3) := mul_nonneg hβ2.le (by have := abs_nonneg N2; linarith only [this, hN3])
        linarith only [h1, h2', h3, hnu1]
      have hwN : |√((2 : ℝ) ^ n) * w| < εr * Fintype.card (Idx n) := by
        rw [hcard]
        apply abs_lt_of_sq_lt_sq _ (by positivity)
        rw [mul_pow, Real.sq_sqrt hN.le]
        have h1 := mul_le_mul_of_nonneg_left hw hN.le
        have h2' : 0 < εr ^ 2 * (2 ^ n) ^ 2 := by positivity
        linarith only [h1, h2']
      have h := Hr n σ hσ0 hσ1 hN2 hβ2n (√((2 : ℝ) ^ n) * w) hwN
      rw [hcard] at h
      have hsq : √((2 : ℝ) ^ n) ≠ 0 := Real.sqrt_ne_zero'.2 hN
      have e1 : √((2 : ℝ) ^ n) * w / √((2 : ℝ) ^ n) = w := by field_simp
      have e2 : (√((2 : ℝ) ^ n) * w) ^ 2 / 2 ^ n = w ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hN.le]; field_simp
      rw [e1, e2] at h
      exact h
    have hCu : 2 * C2 * (1 + τ) + 2 * Cn * (n + 3 * τ) ≤ C * u := by
      rw [hC, hτ]
      linarith [mul_le_mul_of_nonneg_left hu1 hC2.le, mul_le_mul_of_nonneg_left hnu hCnn,
        mul_nonneg hK2_0 hu0]
    have incl := dev_big (G := G) (σ := σ) (l := l) (c := c) (ε := εq / 4) (Cn := Cn) (C2 := C2)
      (τ := τ) (Cu := C * u) (ε' := εr ^ 2 * 2 ^ n / 2) hl0.ne' hCn1 hnode n hC2.le hroot hCu
    refine (measure_mono incl).trans ?_
    have hEn : 0 ≤ exp (-u) := (exp_pos _).le
    -- pieces
    have b1 : μB n {q : ℝ × Zn n | εr ^ 2 * 2 ^ n / 2 < q.1 ^ 2} ≤ ENNReal.ofReal (2 * exp (-u)) := by
      refine (pc_w n _).trans ?_
      rw [two_mul_ofReal]
      apply ENNReal.ofReal_le_ofReal
      have : u ≤ 1 / 4 * (εr ^ 2 * 2 ^ n / 2) := by
        have h1 := mul_le_mul_of_nonneg_right hK1_r hu0
        have h2' : K1 * u ≤ 2 ^ n := by have := abs_nonneg N2; linarith only [this, hx2n, hN3]
        have h3 := mul_le_mul_of_nonneg_left h2' (sq_nonneg εr)
        linarith
      have := exp_neg_le_of this
      linarith
    have b2 : μB n {q | ¬ OnX m0 c n (cplX G σ n q)} ≤ ENNReal.ofReal (2 ^ n * (2 * exp (-u))) := by
      refine (pc_notOnX ha0 hexp hm ht1 h2 hB hV hW hc0.le hpack.1.2 hσ0.ne' hσabs m0 n).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [show c ^ 2 * (2 : ℝ) ^ m0 / 12 = c ^ 2 / 12 * 2 ^ m0 by ring]
      apply notOn_real
      have h1 := mul_le_mul_of_nonneg_right hK1_c hu0
      have h2' : K1 * u ≤ 2 ^ m0 := by have := abs_nonneg N2; linarith only [this, hm0a, hN3]
      have h3 := mul_le_mul_of_nonneg_left h2' (sq_nonneg c)
      linarith
    have b3 : μB n {q : ℝ × Zn n | ¬ OnZ m0 (εq / 4) n q.2} ≤
        ENNReal.ofReal (2 ^ n * (2 * exp (-u))) := by
      refine (pc_notOnZ n hpack.2.1.le m0).trans ?_
      apply ENNReal.ofReal_le_ofReal
      rw [show 1 / 4 * ((εq / 4) ^ 2 * (2 : ℝ) ^ m0) = (εq / 4) ^ 2 / 4 * 2 ^ m0 by ring]
      apply notOn_real
      have h1 := mul_le_mul_of_nonneg_right hpack.2.2 hu0
      have h2' : K1 * u ≤ 2 ^ m0 := by have := abs_nonneg N2; linarith only [this, hm0a, hN3]
      have h3 := mul_le_mul_of_nonneg_left h2' (sq_nonneg (εq / 4))
      linarith
    have b4 : μB n {q : ℝ × Zn n | τ < q.1 ^ 2} ≤ ENNReal.ofReal (2 * exp (-u)) := by
      refine (pc_w n τ).trans ?_
      rw [two_mul_ofReal]
      apply ENNReal.ofReal_le_ofReal
      have := exp_neg_le_of (show u ≤ 1 / 4 * τ by linarith)
      linarith
    have b5 : ∀ i : Idx n, μB n {q : ℝ × Zn n | τ < PZ n q.2 i} ≤
        ENNReal.ofReal (2 ^ n * exp (-u)) := by
      intro i
      refine (pc_Z n i τ).trans ?_
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      gcongr
      linarith
    have b6 : ∀ i : Idx n, μB n {q | OnX m0 c n (cplX G σ n q) ∧ τ < PX m0 n (cplX G σ n q) i} ≤
        ENNReal.ofReal (Amom ^ n * exp (-u)) := by
      intro i
      refine (pc_PX ha0 hexp hm ht1 h2 hB hV hW hpack.1.2 hσ0.ne' hσabs m0 n i τ).trans ?_
      have hA : 0 ≤ Amom ^ n := pow_nonneg (zero_le_one.trans one_le_Amom) n
      rw [← ENNReal.ofReal_mul hA]
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left (exp_neg_le_of (by linarith)) hA
    refine (union_bd (μB n) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ b1 b2 b3 b4 b5 b6 hWXr hWYr).trans ?_
    · positivity
    · positivity
    · positivity
    · positivity
    · positivity
    · exact mul_nonneg (pow_nonneg (zero_le_one.trans one_le_Amom) n) hEn
    · exact mul_nonneg hA0p.le hEn
    · exact mul_nonneg hA0p.le hEn
    · rw [hcard]
      apply ENNReal.ofReal_le_ofReal
      have hX : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hY : (1 : ℝ) ≤ Amom ^ n := one_le_pow₀ one_le_Amom
      have hR : (4 * Amom) ^ n = 2 ^ n * 2 ^ n * Amom ^ n := by
        rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      rw [hR]
      have := total_real hX hY hA0p.le hEn hEs
      linarith

end Kb7

end P99bcb804

end X90_Kb7

section X91_Un1

/-! R4 / Un1 (Q8 unsmoothing, part 1): from a smoothed variable `x' = x + d` (`x ~ G`, `d ~ N(0,v)`
independent) and a fresh standard Gaussian `ξ`, the conditional quantile `uf (x', ξ)` of `x` given `x'`
recovers the pair `(x, d)` exactly in law; vector version by coordinatewise application. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

section Un1

variable (Gm : Measure ℝ) [IsProbabilityMeasure Gm] (v : ℝ≥0)

/-- Joint law of `(x + d, x)`. -/
noncomputable def J1 : Measure (ℝ × ℝ) :=
  (Gm.prod (gaussianReal 0 v)).map (fun p => (p.1 + p.2, p.1))

instance J1_prob : IsProbabilityMeasure (J1 Gm v) := by
  unfold J1; exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Conditional law of `x` given `x' = x + d`. -/
noncomputable def κ1 : Kernel ℝ ℝ :=
  condDistrib (fun q : ℝ × ℝ => q.2) (fun q : ℝ × ℝ => q.1) (J1 Gm v)

instance κ1_markov : IsMarkovKernel (κ1 Gm v) := by
  unfold κ1; infer_instance

/-- The unsmoothing map. -/
noncomputable def uf (p : ℝ × ℝ) : ℝ := qnt (κ1 Gm v p.1) (Phi p.2)

lemma measurable_uf : Measurable (uf Gm v) := measurable_qnt_kernel (κ1 Gm v)

lemma J1_fst : (J1 Gm v).map Prod.fst = Gm ∗ gaussianReal 0 v := by
  rw [J1, Measure.map_map measurable_fst (by fun_prop)]
  rfl

lemma J1_compProd : (Gm ∗ gaussianReal 0 v) ⊗ₘ κ1 Gm v = J1 Gm v := by
  rw [← J1_fst, κ1, compProd_map_condDistrib (by fun_prop)]
  simp

lemma pair_law :
    ((Gm ∗ gaussianReal 0 v).prod (gaussianReal 0 1)).map
        (fun p => (uf Gm v p, p.1 - uf Gm v p)) = Gm.prod (gaussianReal 0 v) := by
  have hm := measurable_uf Gm v
  have e1 : (fun p : ℝ × ℝ => (uf Gm v p, p.1 - uf Gm v p)) =
      (fun q : ℝ × ℝ => (q.2, q.1 - q.2)) ∘ (fun p : ℝ × ℝ => (p.1, uf Gm v p)) := rfl
  rw [e1, ← Measure.map_map (by fun_prop) (measurable_fst.prodMk hm)]
  have e2 : ((Gm ∗ gaussianReal 0 v).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => (p.1, uf Gm v p)) =
      J1 Gm v := by
    rw [← J1_compProd]
    exact map_qnt_kernel _ _
  rw [e2, J1, Measure.map_map (by fun_prop) (by fun_prop)]
  have e3 : ((fun q : ℝ × ℝ => (q.2, q.1 - q.2)) ∘ fun p : ℝ × ℝ => (p.1 + p.2, p.1)) = id := by
    funext p; simp
  rw [e3, Measure.map_id]

end Un1

/-- Coordinatewise application of a pair map with a product law. -/
lemma vec_pair_law {ι : Type} [Fintype ι] (A B C D : Measure ℝ) [IsProbabilityMeasure A]
    [IsProbabilityMeasure B] [IsProbabilityMeasure C] [IsProbabilityMeasure D]
    (h : ℝ × ℝ → ℝ × ℝ) (hh : Measurable h) (hl : (A.prod B).map h = C.prod D) :
    ((Measure.pi fun _ : ι => A).prod (Measure.pi fun _ : ι => B)).map
        (fun w => (fun i => (h (w.1 i, w.2 i)).1, fun i => (h (w.1 i, w.2 i)).2)) =
      (Measure.pi fun _ : ι => C).prod (Measure.pi fun _ : ι => D) := by
  have m1 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => A) (fun _ => B)
  have m2 := measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι (fun _ => C) (fun _ => D)
  rw [← m1.map_eq, ← m2.map_eq, ← hl]
  have hH : Measurable fun w : (ι → ℝ) × (ι → ℝ) =>
      (fun i => (h (w.1 i, w.2 i)).1, fun i => (h (w.1 i, w.2 i)).2) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => measurable_fst.comp (hh.comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)))
    · exact measurable_pi_lambda _ fun i => measurable_snd.comp (hh.comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)))
  rw [Measure.map_map hH (MeasurableEquiv.measurable _)]
  have e : (fun w : (ι → ℝ) × (ι → ℝ) =>
      (fun i => (h (w.1 i, w.2 i)).1, fun i => (h (w.1 i, w.2 i)).2)) ∘
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) =
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι) ∘ (fun z i => h (z i)) := by
    funext z
    simp [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
  have hz : Measurable (fun z : ι → ℝ × ℝ => fun i => h (z i)) :=
    measurable_pi_lambda _ fun i => hh.comp (measurable_pi_apply i)
  rw [e, ← Measure.map_map (MeasurableEquiv.measurable _) hz]
  congr 1
  exact Measure.pi_map_pi (f := fun _ => h) (fun i => hh.aemeasurable)

/-- Gaussian absolute-sum tail. -/
lemma gauss_abs_tail (ι : Type) [Fintype ι] (v : ℝ≥0) {a : ℝ} (ha : 0 < a) (hva : (v : ℝ) * a ^ 2 ≤ 1)
    (u : ℝ) :
    (Measure.pi fun _ : ι => gaussianReal 0 v) {w | u < ∑ i, |w i|} ≤
      ENNReal.ofReal ((2 * exp (1 / 2)) ^ Fintype.card ι * exp (-(a * u))) := by
  have hg : Measurable fun w : ι → ℝ => ∑ i, |w i| :=
    Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).abs
  have hM : ∫⁻ w, ENNReal.ofReal (exp (a * ∑ i, |w i|)) ∂(Measure.pi fun _ : ι => gaussianReal 0 v) ≤
      ENNReal.ofReal ((2 * exp (1 / 2)) ^ Fintype.card ι) := by
    have h1 : ∫⁻ y, ENNReal.ofReal (exp (a * |y|)) ∂(gaussianReal 0 v) ≤
        ENNReal.ofReal (2 * exp (1 / 2)) := by
      refine (absmom_gauss v a).trans ?_
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
    rw [lint_prod_abs, ENNReal.ofReal_pow (by positivity)]
    exact pow_le_pow_left' h1 _
  refine (markov_exp _ hg ha hM u).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity)]

end P99bcb804

end X91_Un1

section X92_Un2

/-! R4 / Un2 (Q8 unsmoothing, part 2): per-block coupling of `pi G` with `pi N(0,1)`:
`σ = e^{-2(n+1)}`, smoothed leaves `X' = cplX`, unsmoothed `X_i = uf (X'_i, ξ_i)`, Gaussian `Z = cplY 1`;
`|ps X - ps Z| ≤ Σ|X' - X| + |ps X' - ps (l Z)| + (l-1) Σ|Z|` with `l = √(1+σ²)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- Smoothing scale of block `n`. -/
noncomputable def σb (n : ℕ) : ℝ := exp (-(2 * ((n : ℝ) + 1)))

noncomputable def vb (n : ℕ) : ℝ≥0 := (σb n ^ 2).toNNReal

lemma σb_pos (n : ℕ) : 0 < σb n := exp_pos _

lemma σb_le_one (n : ℕ) : σb n ≤ 1 := by
  unfold σb; rw [exp_le_one_iff]; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith

lemma σb_inv (n : ℕ) : (σb n)⁻¹ = exp (2 * ((n : ℝ) + 1)) := by
  unfold σb; rw [exp_neg, inv_inv]

lemma vb_coe (n : ℕ) : ((vb n : ℝ≥0) : ℝ) = σb n ^ 2 := by
  unfold vb; rw [Real.coe_toNNReal _ (by positivity)]

/-- Base space measure of the block coupling. -/
noncomputable def PB (n : ℕ) : Measure ((ℝ × Zn n) × (Idx n → ℝ)) :=
  (μB n).prod (Measure.pi fun _ : Idx n => gaussianReal 0 1)

instance PB_prob (n : ℕ) : IsProbabilityMeasure (PB n) := by unfold PB; infer_instance

/-- Pair map (unsmoothed, smoothing noise) per coordinate. -/
noncomputable def hU (Gm : Measure ℝ) [IsProbabilityMeasure Gm] (v : ℝ≥0) (p : ℝ × ℝ) : ℝ × ℝ :=
  (uf Gm v p, p.1 - uf Gm v p)

lemma measurable_hU (Gm : Measure ℝ) [IsProbabilityMeasure Gm] (v : ℝ≥0) : Measurable (hU Gm v) :=
  (measurable_uf Gm v).prodMk (measurable_fst.sub (measurable_uf Gm v))

/-- Vector pair map. -/
noncomputable def HU (Gm : Measure ℝ) [IsProbabilityMeasure Gm] (v : ℝ≥0) (n : ℕ)
    (w : (Idx n → ℝ) × (Idx n → ℝ)) : (Idx n → ℝ) × (Idx n → ℝ) :=
  (fun i => (hU Gm v (w.1 i, w.2 i)).1, fun i => (hU Gm v (w.1 i, w.2 i)).2)

lemma measurable_HU (Gm : Measure ℝ) [IsProbabilityMeasure Gm] (v : ℝ≥0) (n : ℕ) :
    Measurable (HU Gm v n) := by
  have hh := measurable_hU Gm v
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ fun i => measurable_fst.comp (hh.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  · exact measurable_pi_lambda _ fun i => measurable_snd.comp (hh.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))

section Un2

variable {G : Measure ℝ} [IsProbabilityMeasure G]

lemma sL_Idx0 (σ : ℝ) : sL G (Idx 0) σ = G ∗ gaussianReal 0 (σ ^ 2).toNNReal := by
  unfold sL; rw [sumL_Idx0]; simp [card_Idx]

/-- Joint law of (unsmoothed leaves, smoothing noise) on the block base space. -/
lemma un_joint (n : ℕ) :
    (PB n).map (fun ω => HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)) =
      (Measure.pi fun _ : Idx n => G).prod (Measure.pi fun _ : Idx n => gaussianReal 0 (vb n)) := by
  have hσ : σb n ≠ 0 := (σb_pos n).ne'
  have hp := (mpX (G := G) hσ n).prod (MeasurePreserving.id (Measure.pi fun _ : Idx n => gaussianReal 0 1))
  have e : (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)) =
      HU G (vb n) n ∘ Prod.map (cplX G (σb n) n) id := rfl
  rw [e, ← Measure.map_map (measurable_HU G (vb n) n) hp.measurable]
  unfold PB μB at *
  rw [hp.map_eq, sL_Idx0]
  exact vec_pair_law _ _ _ _ (hU G (vb n)) (measurable_hU G (vb n)) (pair_law G (vb n))

lemma un_snd (n : ℕ) :
    (PB n).map (fun ω => cplY 1 n ω.1) = Measure.pi fun _ : Idx n => gaussianReal 0 1 := by
  have hσ : σb n ≠ 0 := (σb_pos n).ne'
  have e : (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => cplY 1 n ω.1) = cplY 1 n ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map (measurable_cplY 1 n) measurable_fst]
  unfold PB
  rw [Measure.map_fst_prod, measure_univ, one_smul, (mpY hσ 1 n).map_eq]
  simp

end Un2

end P99bcb804

end X92_Un2

section X93_Un3

/-! R4 / Un3 (Q8 unsmoothing, part 3): the per-block coupling `QB G n` of `pi G` with `pi N(0,1)`
and its tail bound `QB {∃ k, C (n+1+s) < |ps X k - ps Z k|} ≤ A R^n e^{-s}`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma ps_sub' (n k : ℕ) (f g : Idx n → ℝ) : ps n (fun i => f i - g i) k = ps n f k - ps n g k := by
  unfold ps; rw [Finset.sum_sub_distrib]

lemma ps_mul' (n k : ℕ) (c : ℝ) (f : Idx n → ℝ) : ps n (fun i => c * f i) k = c * ps n f k := by
  unfold ps; rw [Finset.mul_sum]

lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) * 2 ^ n ≤ exp (2 * ((n : ℝ) + 1)) := by
  have h1 : (2 : ℝ) ≤ exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have h2 : (2 : ℝ) ^ (n + 1) ≤ exp 1 ^ (n + 1) := pow_le_pow_left₀ (by norm_num) h1 _
  rw [← Real.exp_nat_mul] at h2
  have h3 : exp (((n + 1 : ℕ) : ℝ) * 1) ≤ exp (2 * ((n : ℝ) + 1)) := by
    rw [exp_le_exp]; push_cast; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  rw [pow_succ] at h2; linarith

lemma kexp (n : ℕ) {s b : ℝ} (hs : 0 ≤ s) (hb : exp (2 * ((n : ℝ) + 1)) ≤ b) :
    (2 * exp (1 / 2)) ^ (2 ^ n) * exp (-(b * ((n : ℝ) + 1 + s))) ≤ exp (-s) := by
  have hb1 : 1 ≤ b := le_trans (one_le_exp (by positivity)) hb
  have he : 2 * exp (1 / 2) ≤ exp 2 := by
    have : (2 : ℝ) ≤ exp (3 / 2) := by have := Real.add_one_le_exp (3 / 2 : ℝ); linarith
    have e : exp 2 = exp (3 / 2) * exp (1 / 2) := by rw [← exp_add]; norm_num
    rw [e]; exact mul_le_mul_of_nonneg_right this (exp_pos _).le
  have hK : (2 * exp (1 / 2)) ^ (2 ^ n) ≤ exp (2 * (2 : ℝ) ^ n) := by
    refine (pow_le_pow_left₀ (by positivity) he _).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  refine (mul_le_mul_of_nonneg_right hK (exp_pos _).le).trans ?_
  rw [← exp_add, exp_le_exp]
  have h2 := two_pow_le_exp n
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have : b * ((n : ℝ) + 1 + s) = b * n + b + b * s := by ring
  have hbn : 0 ≤ b * n := by positivity
  have hbs : s ≤ b * s := le_mul_of_one_le_left hs hb1
  linarith

/-- Per-block coupling of `pi G` with `pi N(0,1)`. -/
noncomputable def QB (G : Measure ℝ) [IsProbabilityMeasure G] (n : ℕ) :
    Measure ((Idx n → ℝ) × (Idx n → ℝ)) :=
  (PB n).map fun ω => ((HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)).1, cplY 1 n ω.1)

section Un3

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

lemma measurable_QBmap (n : ℕ) :
    Measurable fun ω : (ℝ × Zn n) × (Idx n → ℝ) =>
      ((HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)).1, cplY 1 n ω.1) := by
  have hσ : σb n ≠ 0 := (σb_pos n).ne'
  have h1 : Measurable fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G (σb n) n ω.1, ω.2) :=
    (measurable_HU G (vb n) n).comp (((measurable_cplX hσ n).comp measurable_fst).prodMk measurable_snd)
  exact (measurable_fst.comp h1).prodMk ((measurable_cplY 1 n).comp measurable_fst)

instance QB_prob (n : ℕ) : IsProbabilityMeasure (QB G n) := by
  unfold QB; exact Measure.isProbabilityMeasure_map (measurable_QBmap n).aemeasurable

lemma QB_fst (n : ℕ) : (QB G n).map Prod.fst = Measure.pi fun _ : Idx n => G := by
  have hσ : σb n ≠ 0 := (σb_pos n).ne'
  have h1 : Measurable fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G (σb n) n ω.1, ω.2) :=
    (measurable_HU G (vb n) n).comp (((measurable_cplX hσ n).comp measurable_fst).prodMk measurable_snd)
  rw [QB, Measure.map_map measurable_fst (measurable_QBmap n)]
  have e : (Prod.fst ∘ fun ω : (ℝ × Zn n) × (Idx n → ℝ) =>
      ((HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)).1, cplY 1 n ω.1)) =
      Prod.fst ∘ (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G (σb n) n ω.1, ω.2)) := rfl
  rw [e, ← Measure.map_map measurable_fst h1, un_joint, Measure.map_fst_prod, measure_univ, one_smul]

lemma QB_snd (n : ℕ) : (QB G n).map Prod.snd = Measure.pi fun _ : Idx n => gaussianReal 0 1 := by
  rw [QB, Measure.map_map measurable_snd (measurable_QBmap n)]
  exact un_snd n

end Un3

end P99bcb804

end X93_Un3

section X94_Un4

/-! R4 / Un4 (Q8 unsmoothing, part 4): `un_block`, the unsmoothed per-block coupling of `pi G` with
`pi N(0,1)` with tail `A R^n e^{-s}` at level `C (n+1+s)`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

section Un4

variable {G : Measure ℝ} [IsProbabilityMeasure G] {a0 : ℝ}

/-- Deterministic split of the block deviation. -/
lemma un_dev (n k : ℕ) (X' D Z : Idx n → ℝ) (l : ℝ) :
    |ps n (fun i => X' i - D i) k - ps n Z k| ≤
      |ps n X' k - ps n (fun i => l * Z i) k| + ∑ i, |D i| + |l - 1| * ∑ i, |Z i| := by
  rw [ps_sub', ps_mul']
  have h1 := abs_ps_le n D k
  have h2 := abs_ps_le n Z k
  have e : ps n X' k - ps n D k - ps n Z k =
      (ps n X' k - l * ps n Z k) - ps n D k + (l - 1) * ps n Z k := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_sub _ _).trans (add_le_add le_rfl h1)) ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

lemma sqrt_one_add_sq {σ : ℝ} (h0 : 0 ≤ σ) : 1 ≤ √(1 + σ ^ 2) ∧ √(1 + σ ^ 2) - 1 ≤ σ ^ 2 := by
  constructor
  · rw [Real.one_le_sqrt]; nlinarith
  · have : √(1 + σ ^ 2) ≤ 1 + σ ^ 2 / 2 := by
      rw [Real.sqrt_le_left (by positivity)]; linarith [sq_nonneg (σ ^ 2)]
    linarith [sq_nonneg σ]

set_option maxHeartbeats 1000000 in
/-- Q8: unsmoothed per-block coupling of `pi G` with `pi N(0,1)` with exponential tail. -/
theorem un_block (ha0 : 0 < a0)
    (hexp : ∀ a : ℝ, |a| ≤ a0 → Integrable (fun x : ℝ => exp (a * x)) G)
    (hm : ∫ x, x ∂G = 0) (hvar : variance (fun x : ℝ => x) G = 1)
    (p m : ℝ) (v : ℝ≥0) (F2 : Measure ℝ) [IsProbabilityMeasure F2]
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hv0 : 0 < v)
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    {t1 B : ℝ} (ht1 : 0 < t1) (h2 : 2 * t1 < a0) (hB : 0 ≤ B)
    (hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
        iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2)
    (hW : ∀ t ∈ Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B)
    (hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t) :
    ∃ C A R : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ R ∧ ∀ (n : ℕ) (s : ℝ), 0 ≤ s →
      QB G n {q | ∃ k : ℕ, C * (n + 1 + s) < |ps n q.1 k - ps n q.2 k|} ≤
        ENNReal.ofReal (A * R ^ n * exp (-s)) := by
  obtain ⟨C, A, R, hC, hA, hR, H⟩ :=
    block_tail ha0 hexp hm p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  refine ⟨C + 2, A + 2, R, by linarith, by linarith, hR, fun n s hs => ?_⟩
  set σ := σb n with hσdef
  have hσ0 : 0 < σ := σb_pos n
  have hσ1 : σ ≤ 1 := σb_le_one n
  have hσne : σ ≠ 0 := hσ0.ne'
  set l := √(L2s G σ 0) with hldef
  have hL : L2s G σ 0 = 1 + σ ^ 2 := by
    unfold L2s; rw [V_zero ha0 hexp hm hvar]
  obtain ⟨hl1, hl2⟩ := sqrt_one_add_sq hσ0.le
  rw [← hL, ← hldef] at hl1 hl2
  set u : ℝ := (n : ℝ) + 1 + s with hu
  have hu0 : 0 ≤ u := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hQm := measurable_QBmap (G := G) n
  have hXm := measurable_cplX (G := G) hσne n
  have hY1 := measurable_cplY 1 n
  have hYl := measurable_cplY l n
  have h1 : Measurable fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G σ n ω.1, ω.2) :=
    (measurable_HU G (vb n) n).comp ((hXm.comp measurable_fst).prodMk measurable_snd)
  rw [QB, Measure.map_apply hQm (measurableSet_devQ n _)]
  set E1 := {q : (Idx n → ℝ) × (Idx n → ℝ) | ∃ k : ℕ, C * (n + 1 + s) < |ps n q.1 k - ps n q.2 k|}
    with hE1
  set S1 := (fun q : ℝ × Zn n => (cplX G σ n q, cplY l n q)) ⁻¹' E1 with hS1
  have hS1m : MeasurableSet S1 := (hXm.prodMk hYl) (measurableSet_devQ n _)
  set T2 := {w : Idx n → ℝ | u < ∑ i, |w i|} with hT2
  have hT2m : MeasurableSet T2 :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).abs)
  set T3 := {w : Idx n → ℝ | u / σ ^ 2 < ∑ i, |w i|} with hT3
  have hT3m : MeasurableSet T3 :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).abs)
  have hsub : (fun ω : (ℝ × Zn n) × (Idx n → ℝ) =>
      ((HU G (vb n) n (cplX G σ n ω.1, ω.2)).1, cplY 1 n ω.1)) ⁻¹'
        {q | ∃ k : ℕ, (C + 2) * (n + 1 + s) < |ps n q.1 k - ps n q.2 k|} ⊆
      (Prod.fst ⁻¹' S1 ∪ (fun ω : (ℝ × Zn n) × (Idx n → ℝ) =>
        (HU G (vb n) n (cplX G σ n ω.1, ω.2)).2) ⁻¹' T2) ∪
        (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => cplY 1 n ω.1) ⁻¹' T3 := by
    intro ω hω
    obtain ⟨k, hk⟩ := hω
    by_contra hcon
    simp only [mem_union, Set.mem_preimage, not_or] at hcon
    obtain ⟨⟨c1, c2⟩, c3⟩ := hcon
    rw [hS1, Set.mem_preimage, hE1, mem_setOf_eq] at c1
    push_neg at c1
    rw [hT2, mem_setOf_eq, not_lt] at c2
    rw [hT3, mem_setOf_eq, not_lt] at c3
    set X' := cplX G σ n ω.1
    set Z := cplY 1 n ω.1
    set D := (HU G (vb n) n (X', ω.2)).2
    have eX : (HU G (vb n) n (X', ω.2)).1 = fun i => X' i - D i := by
      funext i; simp [D, HU, hU]
    have eY : cplY l n ω.1 = fun i => l * Z i := by
      funext i; simp [Z, cplY]
    have hd := un_dev n k X' D Z l
    rw [← eX, ← eY] at hd
    have c1k := c1 k
    have habs : |l - 1| = l - 1 := abs_of_nonneg (by linarith)
    rw [habs] at hd
    have hZ0 : 0 ≤ ∑ i, |Z i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have c3' : σ ^ 2 * ∑ i, |Z i| ≤ u := by
      have := mul_le_mul_of_nonneg_left c3 (sq_nonneg σ)
      rwa [mul_div_cancel₀ _ (pow_ne_zero 2 hσne)] at this
    have hl3 : (l - 1) * ∑ i, |Z i| ≤ u := (mul_le_mul_of_nonneg_right hl2 hZ0).trans c3'
    have : (C + 2) * u < C * u + u + u := by
      calc (C + 2) * u < _ := hk
        _ ≤ _ := hd
        _ ≤ C * u + u + u := by linarith
    linarith
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add (measure_union_le _ _) le_rfl)) |>.trans ?_
  -- piece 1
  have p1 : PB n (Prod.fst ⁻¹' S1) ≤ ENNReal.ofReal (A * R ^ n * exp (-s)) := by
    rw [← Measure.map_apply measurable_fst hS1m, PB, Measure.map_fst_prod, measure_univ, one_smul]
    have hb := H n σ hσ0 hσ1 (le_of_eq (σb_inv n)) s hs
    unfold cplQ at hb
    rw [Measure.map_apply (hXm.prodMk hYl) (measurableSet_devQ n _)] at hb
    unfold μB; exact hb
  -- piece 2
  have p2 : PB n ((fun ω : (ℝ × Zn n) × (Idx n → ℝ) =>
      (HU G (vb n) n (cplX G σ n ω.1, ω.2)).2) ⁻¹' T2) ≤
      ENNReal.ofReal ((2 * exp (1 / 2)) ^ (2 ^ n) * exp (-(σ⁻¹ * u))) := by
    have e : (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => (HU G (vb n) n (cplX G σ n ω.1, ω.2)).2) =
        Prod.snd ∘ (fun ω : (ℝ × Zn n) × (Idx n → ℝ) => HU G (vb n) n (cplX G σ n ω.1, ω.2)) := rfl
    rw [e, ← Measure.map_apply (measurable_snd.comp h1) hT2m,
      ← Measure.map_map measurable_snd h1, un_joint, Measure.map_snd_prod, measure_univ, one_smul]
    have hva : ((vb n : ℝ≥0) : ℝ) * σ⁻¹ ^ 2 ≤ 1 := by
      rw [vb_coe, ← hσdef, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hσne)]
    have := gauss_abs_tail (Idx n) (vb n) (inv_pos.2 hσ0) hva u
    rwa [card_Idx] at this
  -- piece 3
  have p3 : PB n ((fun ω : (ℝ × Zn n) × (Idx n → ℝ) => cplY 1 n ω.1) ⁻¹' T3) ≤
      ENNReal.ofReal ((2 * exp (1 / 2)) ^ (2 ^ n) * exp (-((σ⁻¹ ^ 2) * u))) := by
    rw [← Measure.map_apply (f := fun ω : (ℝ × Zn n) × (Idx n → ℝ) => cplY 1 n ω.1)
      (hY1.comp measurable_fst) hT3m, un_snd]
    have := gauss_abs_tail (Idx n) 1 (a := 1) one_pos (by norm_num) (u / σ ^ 2)
    rw [card_Idx] at this
    refine this.trans (le_of_eq ?_)
    congr 3
    field_simp
  refine (add_le_add (add_le_add p1 p2) p3).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hσi : exp (2 * ((n : ℝ) + 1)) ≤ σ⁻¹ := le_of_eq (σb_inv n).symm
  have hσi1 : 1 ≤ σ⁻¹ := one_le_inv₀ hσ0 |>.2 hσ1
  have hσi2 : exp (2 * ((n : ℝ) + 1)) ≤ σ⁻¹ ^ 2 := by
    refine hσi.trans ?_
    rw [sq]; exact le_mul_of_one_le_left (by linarith only [hσi1]) hσi1
  have k2 := kexp n hs hσi
  have k3 := kexp n hs hσi2
  rw [← hu] at k2 k3
  have hRn : 1 ≤ R ^ n := one_le_pow₀ hR
  have hes := exp_pos (-s)
  have : exp (-s) ≤ R ^ n * exp (-s) := le_mul_of_one_le_left hes.le hRn
  linarith

end Un4

end P99bcb804

end X94_Un4

section X95_Glue2

/-! P8 part 2: block exponential moment of `Dl`; leaf-order facts for `toNat` and `ps`. -/

open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

lemma toNat_inj : ∀ (n : ℕ) (i j : Idx n), toNat n i = toNat n j → i = j
  | 0, i, j, _ => Subsingleton.elim i j
  | n + 1, Sum.inl i, Sum.inl j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j h]
  | n + 1, Sum.inl i, Sum.inr j, h => by
      simp only [toNat] at h; have := toNat_lt n i; omega
  | n + 1, Sum.inr i, Sum.inl j, h => by
      simp only [toNat] at h; have := toNat_lt n j; omega
  | n + 1, Sum.inr i, Sum.inr j, h => by
      simp only [toNat] at h; rw [toNat_inj n i j (by omega)]

lemma toNat_surj : ∀ (n r : ℕ), r < 2 ^ n → ∃ i : Idx n, toNat n i = r
  | 0, r, hr => ⟨(), by simp [toNat]; omega⟩
  | n + 1, r, hr => by
      by_cases h : r < 2 ^ n
      · obtain ⟨i, hi⟩ := toNat_surj n r h
        exact ⟨Sum.inl i, by simp [toNat, hi]⟩
      · obtain ⟨i, hi⟩ := toNat_surj n (r - 2 ^ n) (by rw [pow_succ] at hr; omega)
        exact ⟨Sum.inr i, by simp only [toNat, hi]; omega⟩

end P99bcb804

end X95_Glue2

section Tail
open MeasureTheory ProbabilityTheory Real Set Filter Topology Finset
open scoped NNReal ENNReal

namespace P99bcb804

/-- In-order positions identify the dyadic index type with `Fin (2^n)`. -/
noncomputable def eFin (n : ℕ) : Idx n ≃ Fin (2 ^ n) :=
  Equiv.ofBijective (fun i => ⟨toNat n i, toNat_lt n i⟩)
    ⟨fun i j h => toNat_inj n i j (congrArg Fin.val h),
     fun r => by
       obtain ⟨i, hi⟩ := toNat_surj n r.1 r.2
       exact ⟨i, Fin.ext hi⟩⟩

lemma eFin_val (n : ℕ) (i : Idx n) : ((eFin n i : Fin (2 ^ n)) : ℕ) = toNat n i := rfl

lemma ps_eFin (n : ℕ) (g : Fin (2 ^ n) → ℝ) (k : ℕ) :
    ps n (fun i => g (eFin n i)) k =
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ n) => (i : ℕ) < k), g i := by
  unfold ps
  rw [Finset.sum_filter, Finset.sum_filter]
  exact Equiv.sum_comp (eFin n) (fun j : Fin (2 ^ n) => if (j : ℕ) < k then g j else 0)

lemma pi_eFin (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (Measure.pi (fun _ : Fin (2 ^ n) => F)).map (fun g : Fin (2 ^ n) → ℝ => fun i => g (eFin n i)) =
      Measure.pi (fun _ : Idx n => F) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Idx n => F) (eFin n).symm).map_eq
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Idx n => ℝ) (eFin n).symm) :
      (Fin (2 ^ n) → ℝ) → (Idx n → ℝ)) = fun g i => g (eFin n i) := by
    funext g i
    have := Equiv.piCongrLeft_apply_apply (fun _ : Idx n => ℝ) (eFin n).symm g (eFin n i)
    simp only [Equiv.symm_apply_apply] at this
    rw [← this]; rfl
  rw [hf] at h
  exact h

end P99bcb804

namespace P99bcb804

lemma pi_eFin_symm (n : ℕ) (F : Measure ℝ) [IsProbabilityMeasure F] :
    (Measure.pi (fun _ : Idx n => F)).map (fun g : Idx n → ℝ => fun j => g ((eFin n).symm j)) =
      Measure.pi (fun _ : Fin (2 ^ n) => F) := by
  have h := (measurePreserving_piCongrLeft (fun _ : Fin (2 ^ n) => F) (eFin n)).map_eq
  have hf : (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin (2 ^ n) => ℝ) (eFin n)) :
      (Idx n → ℝ) → (Fin (2 ^ n) → ℝ)) = fun g j => g ((eFin n).symm j) := by
    funext g j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (2 ^ n) => ℝ) (eFin n) g ((eFin n).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]; rfl
  rw [hf] at h
  exact h

/-- Export of a dyadic block tail bound from `Idx n` to `Fin (2^n)` in KMT (1.1) form. -/
theorem dy_of_idx (F : Measure ℝ) [IsProbabilityMeasure F] {C c A R b : ℝ} (hC : 0 < C)
    (hc : 0 < c) (hA : 0 < A) (hR : 1 ≤ R) (hb : 0 ≤ b)
    (H : ∀ n : ℕ, ∃ Q : Measure ((Idx n → ℝ) × (Idx n → ℝ)), IsProbabilityMeasure Q ∧
      Q.map Prod.fst = Measure.pi (fun _ : Idx n => F) ∧
      Q.map Prod.snd = Measure.pi (fun _ : Idx n => gaussianReal 0 1) ∧
      ∀ s : ℝ, 0 ≤ s → Q {q | ∃ k : ℕ, C * (n + b + s) < |ps n q.1 k - ps n q.2 k|} ≤
        ENNReal.ofReal (A * R ^ n * Real.exp (-(c * s)))) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => F) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlR : 0 ≤ Real.log R := Real.log_nonneg hR
  set C' : ℝ := C * (2 + Real.log R / c) / Real.log 2 with hC'
  set K : ℝ := 2 * (A * Real.exp (c * b) + Real.exp (c * b)) with hKdef
  refine ⟨C', K, c / C, by positivity, by positivity, by positivity, ?_⟩
  intro N
  obtain ⟨Q, hQp, hQ1, hQ2, hQ3⟩ := H N
  set T : (Idx N → ℝ) × (Idx N → ℝ) → (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) :=
    fun q => (fun j => q.1 ((eFin N).symm j), fun j => q.2 ((eFin N).symm j)) with hT
  have hTm : Measurable T := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_fst
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd
  refine ⟨Q.map T, Measure.isProbabilityMeasure_map hTm.aemeasurable, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hTm]
    have : (Prod.fst ∘ T) = (fun g : Idx N → ℝ => fun j => g ((eFin N).symm j)) ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_fst,
      hQ1, pi_eFin_symm]
  · rw [Measure.map_map measurable_snd hTm]
    have : (Prod.snd ∘ T) = (fun g : Idx N → ℝ => fun j => g ((eFin N).symm j)) ∘ Prod.snd := rfl
    rw [this, ← Measure.map_map (measurable_pi_lambda _ fun i => measurable_pi_apply _) measurable_snd,
      hQ2, pi_eFin_symm]
  intro x hx
  have hps : ∀ (g : Idx N → ℝ) (k : ℕ),
      (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), g ((eFin N).symm i)) =
        ps N g k := by
    intro g k
    have := ps_eFin N (fun j => g ((eFin N).symm j)) k
    simp only [Equiv.symm_apply_apply] at this
    exact this.symm
  have hmeasF : MeasurableSet {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
          (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} := by
    have : {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
          (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} =
        ⋃ k : ℕ, ⋃ (_ : 1 ≤ k ∧ k ≤ 2 ^ N), {q : (Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ) |
          C' * Real.log ((2 ^ N : ℕ) : ℝ) + x <
          |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
            (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} := by
      ext q; simp [and_assoc]
    rw [this]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const (by fun_prop)
  rw [Measure.map_apply hTm hmeasF]
  have hQ1' : (Q : Measure _) Set.univ = 1 := measure_univ
  by_cases hxb : x < C * b
  · -- small x: the bound exceeds 1
    refine lt_of_le_of_lt (prob_le_one) ?_
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
    have h1 : Real.exp (-(c * b)) ≤ Real.exp (-(c / C) * x) := by
      refine Real.exp_le_exp.2 ?_
      have : c / C * x ≤ c / C * (C * b) := mul_le_mul_of_nonneg_left hxb.le (by positivity)
      rw [show c / C * (C * b) = c * b by field_simp] at this
      linarith
    have h2 : Real.exp (c * b) * Real.exp (-(c * b)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 : 0 < A * Real.exp (c * b) * Real.exp (-(c / C) * x) := by positivity
    have h4 : Real.exp (c * b) * Real.exp (-(c * b)) ≤ Real.exp (c * b) * Real.exp (-(c / C) * x) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hKdef]
    linarith
  · push_neg at hxb
    set s : ℝ := N * (1 + Real.log R / c) + (x - C * b) / C with hs
    have hs0 : 0 ≤ s := by
      have : 0 ≤ (x - C * b) / C := div_nonneg (by linarith) hC.le
      positivity
    have hthr : C * (N + b + s) = C' * Real.log ((2 ^ N : ℕ) : ℝ) + x := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hC', hs]
      field_simp
      ring
    refine lt_of_le_of_lt (measure_mono ?_) (lt_of_le_of_lt (hQ3 s hs0) ?_)
    · intro q hq
      obtain ⟨k, -, -, hk⟩ := hq
      refine ⟨k, ?_⟩
      rw [hthr]
      simpa only [hT, hps] using hk
    · refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
      have hRn : R ^ N = Real.exp (N * Real.log R) := by
        rw [← Real.log_pow, Real.exp_log (by positivity)]
      have he : R ^ N * Real.exp (-(c * s)) ≤ Real.exp (c * b) * Real.exp (-(c / C) * x) := by
        rw [hRn, ← Real.exp_add, ← Real.exp_add]
        refine Real.exp_le_exp.2 ?_
        have key : (N : ℝ) * Real.log R + -(c * s) = -(c * N) + (c * b + -(c / C) * x) := by
          rw [hs]; field_simp; ring
        rw [key]
        have : 0 ≤ c * N := by positivity
        linarith
      have h5 : 0 < A * Real.exp (c * b) * Real.exp (-(c / C) * x) := by positivity
      rw [mul_assoc, hKdef]
      have h6 := mul_le_mul_of_nonneg_left he hA.le
      linarith [h5, h6, mul_pos (Real.exp_pos (c * b)) (Real.exp_pos (-(c / C) * x))]

end P99bcb804

end Tail

section GaussMain
open MeasureTheory ProbabilityTheory Real Set Filter Topology
namespace P99bcb804
theorem gauss_main (F2 : Measure ℝ) [IsProbabilityMeasure F2] (p m : ℝ)
    (v : NNReal) (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : v ≠ 0) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    (hexp : (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) G))
    (hm : ∫ x, x ∂G = 0) (hvar : variance (fun x : ℝ => x) G = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => G) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  obtain ⟨a0, ha0, hexp⟩ := hexp
  obtain ⟨t1', B, ht1', h2', hB, hcum⟩ := P99bcb804.cum_local ha0 hexp hm hvar
  obtain ⟨t2, ht2, hpt2⟩ := P99bcb804.pt_lower_g ha0 hexp m v
  set t1 := min t1' t2 with ht1def
  have ht1 : 0 < t1 := lt_min ht1' ht2
  have ht1a : t1 ≤ t1' := min_le_left _ _
  have ht1b : t1 ≤ t2 := min_le_right _ _
  have h2 : 2 * t1 < a0 := by linarith
  have hV : ∀ t : ℝ, |t| ≤ t1 → 1 / 2 ≤ iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ∧
      iteratedDeriv 2 (cgf (fun x : ℝ => x) G) t ≤ 2 := by
    intro t ht
    have := abs_le.1 ht
    exact (hcum t ⟨by linarith, by linarith⟩).1
  have hW : ∀ t ∈ Set.Icc (-(2 * t1)) (2 * t1), |iteratedDeriv 3 (cgf (fun x : ℝ => x) G) t| ≤ B := by
    intro t ht
    exact (hcum t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2
  have hpt : ∀ t : ℝ, |t| ≤ t1 →
      1 / 2 ≤ mgf (fun x : ℝ => x) (gaussianReal m v) t / mgf (fun x : ℝ => x) G t :=
    fun t ht => hpt2 t (ht.trans ht1b)
  have hv0 : 0 < v := pos_iff_ne_zero.2 hv
  obtain ⟨C, A, R, hC, hA, hR, H⟩ :=
    P99bcb804.un_block ha0 hexp hm hvar p m v F2 hp0 hp1 hv0 hG ht1 h2 hB hV hW hpt
  refine P99bcb804.dy_of_idx G (c := 1) (b := 1) hC one_pos hA hR zero_le_one fun n =>
    ⟨P99bcb804.QB G n, P99bcb804.QB_prob n, P99bcb804.QB_fst n, P99bcb804.QB_snd n, fun s hs => ?_⟩
  rw [one_mul]
  exact H n s hs
end P99bcb804
end GaussMain

end P99Hyps

open MeasureTheory ProbabilityTheory in

open MeasureTheory ProbabilityTheory in
theorem solution (F2 : Measure ℝ) [IsProbabilityMeasure F2] (p m : ℝ)
    (v : NNReal) (hp0 : 0 < p) (hp1 : p ≤ 1) (hv : v ≠ 0) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : G = ENNReal.ofReal p • gaussianReal m v + ENNReal.ofReal (1 - p) • F2)
    (hexp : (∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, |a| ≤ a₀ → Integrable (fun x : ℝ => Real.exp (a * x)) G))
    (hm : ∫ x, x ∂G = 0) (hvar : variance (fun x : ℝ => x) G = 1) :
    ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧ ∀ N : ℕ,
      ∃ Q : Measure ((Fin (2 ^ N) → ℝ) × (Fin (2 ^ N) → ℝ)), IsProbabilityMeasure Q ∧
        Q.map Prod.fst = Measure.pi (fun _ : Fin (2 ^ N) => G) ∧
        Q.map Prod.snd = Measure.pi (fun _ : Fin (2 ^ N) => gaussianReal 0 1) ∧
        ∀ x : ℝ, 0 < x →
          Q {q | ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ^ N ∧ C * Real.log ((2 ^ N : ℕ) : ℝ) + x <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.1 i) -
              (∑ i ∈ Finset.univ.filter (fun i : Fin (2 ^ N) => (i : ℕ) < k), q.2 i)|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  exact P99bcb804.gauss_main F2 p m v hp0 hp1 hv G hG hexp hm hvar
