-- Prove2me | solution 1 for DistCov.Hilbert.gaussian_series
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T18:58:16.257455+00:00
-- url     : https://prove2.me/submissions/71792834-f75a-4a99-b9da-fb0dacf4521f

import Definitions.Def_DistCov_Hilbert_Setting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace DistCovGS
open DistCov.Hilbert
abbrev Ω := ℕ → ℝ
abbrev H := DistCov.Indep.L2N

instance : IsProbabilityMeasure rho := by
  unfold rho
  infer_instance

def X (u : H) (n : ℕ) (w : Ω) : ℝ := u n * w n

def S (u : H) (N : ℕ) (w : Ω) : ℝ := ∑ n ∈ Finset.range N, X u n w

def q (u : H) (n : ℕ) : ℝ≥0 := ⟨u n ^ 2, sq_nonneg _⟩

def v (u : H) (s : Finset ℕ) : ℝ≥0 := ∑ n ∈ s, q u n

@[fun_prop] lemma X_meas (u : H) (n : ℕ) : Measurable (X u n) := by
  unfold X
  fun_prop

@[fun_prop] lemma S_meas (u : H) (N : ℕ) : Measurable (S u N) := by
  unfold S
  exact Finset.measurable_sum _ fun n hn => X_meas u n

lemma X_indep (u : H) : iIndepFun (X u) rho := by
  exact iIndepFun_infinitePi (P := fun _ : ℕ => gaussianReal 0 1)
    (X := fun n x => u n * x) (by intro n; fun_prop)

lemma X_law (u : H) (n : ℕ) : rho.map (X u n) = gaussianReal 0 (q u n) := by
  have he : X u n = (fun x : ℝ => u n * x) ∘ (fun w : Ω => w n) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [rho, Measure.infinitePi_map_eval, gaussianReal_map_const_mul]
  simp [q, NNReal.mk, mul_one]

lemma sum_law (u : H) (s : Finset ℕ) :
    rho.map (fun w => ∑ n ∈ s, X u n w) = gaussianReal 0 (v u s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v, gaussianReal_zero_var]
  | @insert n s hn ih =>
    have hi := (X_indep u).indepFun_finsetSum_of_notMem (X_meas u) hn
    have ih' : rho.map (∑ j ∈ s, X u j) = gaussianReal 0 (v u s) := by
      simpa only [Finset.sum_fn] using ih
    have hl := gaussianReal_add_gaussianReal_of_indepFun hi ih' (X_law u n)
    simpa [v, Finset.sum_insert hn, add_comm, Pi.add_def, Finset.sum_fn] using hl

lemma gaussian_integrable (a : ℝ≥0) : Integrable (fun x : ℝ => x) (gaussianReal 0 a) :=
  (memLp_id_gaussianReal (μ := 0) (v := a) 1).integrable (by norm_num)

lemma law_integrable {f : Ω → ℝ} (hm : AEMeasurable f rho) (a : ℝ≥0)
    (hl : rho.map f = gaussianReal 0 a) : Integrable f rho := by
  have h := gaussian_integrable a
  rw [← hl] at h
  exact h.comp_aemeasurable hm

lemma gaussian_abs (a : ℝ≥0) :
    (∫ x : ℝ, |x| ∂gaussianReal 0 a) = cGauss * (a.sqrt : ℝ) := by
  have hl : (gaussianReal 0 1).map (fun x : ℝ => (a.sqrt : ℝ) * x) = gaussianReal 0 a := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · apply NNReal.coe_injective
      simp
  rw [← hl, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg a.sqrt)]
  rw [integral_const_mul]
  exact mul_comm _ _

lemma law_abs {f : Ω → ℝ} (hm : AEMeasurable f rho) (a : ℝ≥0)
    (hl : rho.map f = gaussianReal 0 a) :
    (∫ w, |f w| ∂rho) = cGauss * (a.sqrt : ℝ) := by
  rw [← gaussian_abs a, ← hl, integral_map hm (by fun_prop)]

lemma square_sum_tendsto (u : H) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, u n ^ 2) atTop (𝓝 (‖u‖ ^ 2)) := by
  have h := (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) u).tendsto_sum_nat
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

lemma var_coe (u : H) (s : Finset ℕ) : (v u s : ℝ) = ∑ n ∈ s, u n ^ 2 := by
  unfold v
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rfl

lemma var_bound (u : H) (s : Finset ℕ) : (v u s : ℝ) ≤ ‖u‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2 : ENNReal).toReal) u s
  simpa only [var_coe, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

lemma law_of_convergence (u : H)
    (hc : ∀ᵐ w ∂rho, Tendsto (fun N => S u N w) atTop (𝓝 (wEval w u))) :
    rho.map (fun w => wEval w u) = gaussianReal 0 (‖u‖₊ ^ 2) := by
  have hm : AEMeasurable (fun w => wEval w u) rho :=
    aemeasurable_of_tendsto_metrizable_ae' (fun N => (S_meas u N).aemeasurable) hc
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply_real, integral_map hm (by fun_prop), charFun_gaussianReal]
  have hD : Tendsto (fun N => ∫ w, Complex.exp ((t : ℂ) * (S u N w : ℂ) * Complex.I) ∂rho)
      atTop (𝓝 (∫ w, Complex.exp ((t : ℂ) * (wEval w u : ℂ) * Complex.I) ∂rho)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro N
      exact ((by fun_prop : Measurable (fun w =>
        Complex.exp ((t : ℂ) * (S u N w : ℂ) * Complex.I)))).aestronglyMeasurable
    · exact integrable_const 1
    · intro N
      exact Eventually.of_forall fun w => by
        simpa only [← Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * S u N w)).le
    · filter_upwards [hc] with w hw
      exact Complex.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hw)).mul
          tendsto_const_nhds)
  have he : ∀ N, (∫ w, Complex.exp ((t : ℂ) * (S u N w : ℂ) * Complex.I) ∂rho) =
      Complex.exp (-(v u (Finset.range N) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    intro N
    rw [← integral_map (f := fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
      (S_meas u N).aemeasurable (by fun_prop)]
    rw [← charFun_apply_real]
    rw [show rho.map (S u N) = gaussianReal 0 (v u (Finset.range N)) from sum_law u _,
      charFun_gaussianReal]
    simp [neg_div]
  have hV : Tendsto (fun N => (v u (Finset.range N) : ℝ)) atTop (𝓝 (‖u‖ ^ 2)) := by
    simpa only [var_coe] using square_sum_tendsto u
  have hE : Tendsto (fun N => Complex.exp (-((v u (Finset.range N) : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))
      atTop (𝓝 (Complex.exp (-((‖u‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) :=
    Complex.continuous_exp.continuousAt.tendsto.comp
    (((Complex.continuous_ofReal.continuousAt.tendsto.comp hV).neg.mul tendsto_const_nhds).div_const 2)
  have hE' : Tendsto (fun N => ∫ w, Complex.exp ((t : ℂ) * (S u N w : ℂ) * Complex.I) ∂rho)
      atTop (𝓝 (Complex.exp (-((‖u‖ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    simpa only [he] using hE
  simpa [Complex.ofReal_pow, neg_mul, neg_div] using tendsto_nhds_unique hD hE'

lemma S_integrable (u : H) (N : ℕ) : Integrable (S u N) rho :=
  law_integrable (S_meas u N).aemeasurable _ (sum_law u (Finset.range N))

lemma S_L1_bound (u : H) (N : ℕ) :
    eLpNorm (S u N) 1 rho ≤ ENNReal.ofReal (cGauss * ‖u‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (S_integrable u N)]
  simp_rw [Real.norm_eq_abs]
  rw [law_abs (S_meas u N).aemeasurable _ (sum_law u (Finset.range N))]
  apply ENNReal.ofReal_le_ofReal
  have hs : ((v u (Finset.range N)).sqrt : ℝ) ≤ ‖u‖ := by
    have he : ((v u (Finset.range N)).sqrt : ℝ) ^ 2 = (v u (Finset.range N) : ℝ) := by
      exact_mod_cast NNReal.sq_sqrt (v u (Finset.range N))
    nlinarith [var_bound u (Finset.range N), norm_nonneg u,
      NNReal.coe_nonneg ((v u (Finset.range N)).sqrt)]
  exact mul_le_mul_of_nonneg_left hs (integral_nonneg fun z => abs_nonneg z)

lemma X_mean_zero (u : H) (n : ℕ) : (∫ w, X u n w ∂rho) = 0 := by
  have hl : HasLaw (X u n) (gaussianReal 0 (q u n)) rho :=
    ⟨(X_meas u n).aemeasurable, X_law u n⟩
  simpa only [integral_id_gaussianReal] using hl.integral_eq

lemma S_martingale (u : H) :
    Martingale (fun N => S u (N + 1))
      (Filtration.natural (X u) (fun n => (X_meas u n).stronglyMeasurable)) rho := by
  let F := Filtration.natural (X u) (fun n => (X_meas u n).stronglyMeasurable)
  apply martingale_of_condExp_sub_eq_zero_nat
  · intro N
    have he : S u (N + 1) = ∑ n ∈ Finset.range (N + 1), X u n := by
      funext w
      simp only [S, Finset.sum_apply]
    change StronglyMeasurable[F N] (S u (N + 1))
    rw [he]
    apply Finset.stronglyMeasurable_sum
    intro n hn
    have hn' : n ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact ((Filtration.stronglyAdapted_natural
      (fun n => (X_meas u n).stronglyMeasurable)) n).mono (F.mono hn')
  · intro N
    exact S_integrable u (N + 1)
  · intro N
    have he : S u (N + 1 + 1) - S u (N + 1) = X u (N + 1) := by
      funext w
      simp [S, Finset.sum_range_succ]
    rw [he]
    have h := (X_indep u).condExp_natural_ae_eq_of_lt
      (fun n => (X_meas u n).stronglyMeasurable) (Nat.lt_succ_self N)
    filter_upwards [h] with w hw
    simpa only [X_mean_zero, Pi.zero_apply] using hw

lemma S_converges (u : H) :
    ∀ᵐ w ∂rho, Tendsto (fun N => S u N w) atTop (𝓝 (wEval w u)) := by
  have hc := (S_martingale u).submartingale.exists_ae_tendsto_of_bdd
    (fun N => S_L1_bound u (N + 1))
  filter_upwards [hc] with w hw
  obtain ⟨a, ha⟩ := hw
  have hS : Tendsto (fun N => S u N w) atTop (𝓝 a) :=
    (tendsto_add_atTop_iff_nat 1).mp ha
  have he : wEval w u = a := hS.limsup_eq
  rwa [he]

lemma gaussian_series (u : H) :
    (∀ᵐ w ∂rho, Tendsto (fun N => S u N w) atTop (𝓝 (wEval w u))) ∧
    rho.map (fun w => wEval w u) = gaussianReal 0 (‖u‖₊ ^ 2) ∧
    Integrable (fun w => wEval w u) rho ∧
    (∫ w, |wEval w u| ∂rho) = cGauss * ‖u‖ := by
  have hc := S_converges u
  have hm := aemeasurable_of_tendsto_metrizable_ae'
    (fun N => (S_meas u N).aemeasurable) hc
  have hl := law_of_convergence u hc
  refine ⟨hc, hl, law_integrable hm _ hl, ?_⟩
  simpa using law_abs hm _ hl

end DistCovGS

#print axioms DistCovGS.sum_law
#print axioms DistCovGS.law_of_convergence

open DistCov.Hilbert

theorem solution (u : DistCov.Indep.L2N) :
    (∀ᵐ w ∂rho, Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, u n * w n)
      Filter.atTop (nhds (wEval w u))) ∧
    rho.map (fun w => wEval w u) = gaussianReal 0 (‖u‖₊ ^ 2) ∧
    Integrable (fun w => wEval w u) rho ∧
    (∫ w, |wEval w u| ∂rho) = cGauss * ‖u‖ := by
  exact DistCovGS.gaussian_series u

#print axioms solution
