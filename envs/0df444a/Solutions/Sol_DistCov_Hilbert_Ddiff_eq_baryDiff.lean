-- Prove2me | solution 1 for DistCov.Hilbert.Ddiff_eq_baryDiff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T19:49:20.570439+00:00
-- url     : https://prove2.me/submissions/8ed61609-b2d3-41fb-af88-d35f47ba7ea2

import Theorems.Thm_DistCov_Hilbert_gaussEmb_isometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology NNReal

namespace DistCovBary
open DistCov.Hilbert
abbrev H := DistCov.Indep.L2N
abbrev Ω := ℕ → ℝ
abbrev P := Ω × ℝ
abbrev m : Measure P := rho.prod volume
local instance : IsProbabilityMeasure rho := by unfold rho; infer_instance

def e (n : ℕ) : H := lp.single 2 n (1 : ℝ)

def trunc (N : ℕ) (u : H) : H := ∑ n ∈ Finset.range N, lp.single 2 n (u n)

lemma trunc_tendsto (u : H) : Tendsto (fun N => trunc N u) atTop (𝓝 u) :=
  (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) u).tendsto_sum_nat

lemma single_eq_smul (u : H) (n : ℕ) : lp.single 2 n (u n) = u n • e n := by
  simpa [e] using (lp.single_smul (E := fun _ : ℕ => ℝ) 2 n (u n) (1 : ℝ))

lemma separable_H : SeparableSpace H := by
  let S := Submodule.span ℝ (Set.range e)
  have hs : IsSeparable (closure (S : Set H)) := (Set.countable_range e).isSeparable.span.closure
  apply isSeparable_univ_iff.mp
  apply hs.mono
  intro u hu
  apply mem_closure_of_tendsto (trunc_tendsto u)
  exact Eventually.of_forall fun N => S.sum_mem fun n hn => by
    rw [single_eq_smul]
    exact S.smul_mem _ (Submodule.subset_span ⟨n, rfl⟩)

local instance : SeparableSpace H := separable_H

def f (u : H) (p : P) : ℝ := gaussEmb u p

def B (μ : Measure H) (p : P) : ℝ := ∫ u, f u p ∂μ

def A (μ : Measure H) (p : P) : ℝ := ∫ u, f u p ^ 2 ∂μ

lemma c_pos : 0 < cGauss := by
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  unfold cGauss
  apply (integral_pos_iff_support_of_nonneg (fun z => abs_nonneg z) hi).mpr
  have he : Function.support (fun z : ℝ => |z|) = ({0} : Set ℝ)ᶜ := by
    ext z; simp [Function.support]
  rw [he, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

@[fun_prop] lemma eval_meas : Measurable (fun q : H × Ω => wEval q.2 q.1) := by
  unfold wEval
  apply Measurable.limsup
  intro N
  apply Finset.measurable_sum
  intro n hn
  have hc : Continuous (fun u : H => u n) :=
    (continuous_apply n).comp lp.uniformContinuous_coe.continuous
  exact (hc.measurable.comp measurable_fst).mul ((measurable_pi_apply n).comp measurable_snd)

@[fun_prop] lemma f_meas : Measurable (fun q : H × P => f q.1 q.2) := by
  have he : Measurable (fun q : H × P => wEval q.2.1 q.1) :=
    @Measurable.comp (H × P) (H × Ω) ℝ _ _ _
      (fun q => wEval q.2 q.1) (fun q => (q.1, q.2.1)) eval_meas
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have ht : MeasurableSet {q : H × P | wEval q.2.1 q.1 / cGauss ≤ q.2.2} :=
    measurableSet_le (he.div_const cGauss) (measurable_snd.comp measurable_snd)
  have hb : MeasurableSet {q : H × P | (0 : ℝ) ≤ q.2.2} :=
    measurableSet_le measurable_const (measurable_snd.comp measurable_snd)
  have hi : Measurable (fun q : H × P =>
      ({q : H × P | wEval q.2.1 q.1 / cGauss ≤ q.2.2}.indicator (fun _ => (1 : ℝ)) q) -
      ({q : H × P | (0 : ℝ) ≤ q.2.2}.indicator (fun _ => (1 : ℝ)) q)) :=
    (measurable_const.indicator ht).sub (measurable_const.indicator hb)
  convert hi using 1
  ext q
  simp only [f, gaussEmb, Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq]

@[fun_prop] lemma f_left_meas (p : P) : Measurable (fun u : H => f u p) :=
  @Measurable.comp H (H × P) ℝ _ _ _ (fun q => f q.1 q.2) (fun u => (u, p))
    f_meas (measurable_id.prodMk measurable_const)

@[fun_prop] lemma f_right_meas (u : H) : Measurable (f u) :=
  @Measurable.comp P (H × P) ℝ _ _ _ (fun q => f q.1 q.2) (fun p => (u, p))
    f_meas (measurable_const.prodMk measurable_id)

lemma f_bound (u : H) (p : P) : |f u p| ≤ 1 := by
  unfold f gaussEmb
  simp only [Set.indicator, Set.mem_Ici]
  split_ifs <;> norm_num

lemma f_zero (p : P) : f (0 : H) p = 0 := by
  have hw : wEval p.1 (0 : ℕ → ℝ) = 0 := by
    unfold wEval
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact limsup_const (f := atTop) (0 : ℝ)
  simp only [f, gaussEmb, lp.coeFn_zero, hw, zero_div, sub_self]

lemma f_sq_integrable (u : H) : Integrable (fun p => f u p ^ 2) m := by
  have h : Integrable (fun p => (f u p - f 0 p)^2) m := (gaussEmb_isometry u 0).1
  simpa only [f_zero, sub_zero] using h

lemma f_sq_integral (u : H) : ∫ p, f u p ^ 2 ∂m = ‖u‖ := by
  have h : ∫ p, (f u p - f 0 p)^2 ∂m = ‖u - 0‖ := (gaussEmb_isometry u 0).2.1
  simpa only [f_zero, sub_zero] using h

lemma left_integrable (μ : Measure H) [IsFiniteMeasure μ] (p : P) :
    Integrable (fun u => f u p) μ :=
  (integrable_const (1 : ℝ)).mono' (f_left_meas p).aestronglyMeasurable
    (Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs] using f_bound u p)

lemma left_sq_integrable (μ : Measure H) [IsFiniteMeasure μ] (p : P) :
    Integrable (fun u => f u p ^ 2) μ := by
  apply (integrable_const (1 : ℝ)).mono' ((f_left_meas p).pow_const 2).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := f_bound u p
  nlinarith [sq_abs (f u p), abs_nonneg (f u p)]

lemma norm_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (h : DistCov.Indep.FiniteFirstMoment μ) : Integrable (fun u => ‖u‖) μ := by
  obtain ⟨o, ho⟩ := h
  apply (ho.add (integrable_const ‖o‖)).mono' continuous_norm.measurable.aestronglyMeasurable
  filter_upwards [] with u
  rw [norm_norm]
  calc ‖u‖ ≤ ‖u - o‖ + ‖o‖ := by simpa only [sub_add_cancel] using norm_add_le (u - o) o
       _ = dist o u + ‖o‖ := by rw [← dist_eq_norm, dist_comm]

@[fun_prop] lemma B_meas (μ : Measure H) [IsFiniteMeasure μ] : Measurable (B μ) :=
  f_meas.stronglyMeasurable.integral_prod_left.measurable

@[fun_prop] lemma A_meas (μ : Measure H) [IsFiniteMeasure μ] : Measurable (A μ) :=
  (f_meas.pow_const 2).stronglyMeasurable.integral_prod_left.measurable

lemma square_kernel_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (h : DistCov.Indep.FiniteFirstMoment μ) :
    Integrable (fun q : H × P => f q.1 q.2 ^ 2) (μ.prod m) := by
  apply (integrable_prod_iff (f_meas.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall f_sq_integrable, ?_⟩
  have he : (fun u => ∫ p, ‖f u p ^ 2‖ ∂m) = (fun u : H => ‖u‖) := by
    funext u
    simp only [Real.norm_eq_abs, abs_pow, sq_abs, f_sq_integral]
  rw [he]
  exact norm_integrable μ h

lemma A_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (h : DistCov.Indep.FiniteFirstMoment μ) : Integrable (A μ) m :=
  (square_kernel_integrable μ h).integral_prod_right

lemma A_integral (μ : Measure H) [IsProbabilityMeasure μ]
    (h : DistCov.Indep.FiniteFirstMoment μ) : ∫ p, A μ p ∂m = ∫ u, ‖u‖ ∂μ := by
  change (∫ p, ∫ u, f u p ^ 2 ∂μ ∂m) = _
  rw [← integral_prod_symm _ (square_kernel_integrable μ h),
    integral_prod _ (square_kernel_integrable μ h)]
  simp only [f_sq_integral]

lemma B_sq_le_A (μ : Measure H) [IsProbabilityMeasure μ] (p : P) : B μ p ^ 2 ≤ A μ p := by
  have hi := left_integrable μ p
  have hsq := left_sq_integrable μ p
  have he : (fun u => (f u p - B μ p) ^ 2) =
      (fun u => (f u p ^ 2 - (2 * B μ p) * f u p) + B μ p ^ 2) := by
    funext u; ring
  have hn : 0 ≤ ∫ u, (f u p - B μ p) ^ 2 ∂μ := integral_nonneg fun u => sq_nonneg _
  have hlin : Integrable (fun u => (2 * B μ p) * f u p) μ := hi.const_mul _
  have hsub : Integrable (fun u => f u p ^ 2 - (2 * B μ p) * f u p) μ := hsq.sub hlin
  rw [he, integral_add hsub (integrable_const (B μ p ^ 2)),
    integral_sub hsq hlin, integral_const_mul, integral_const] at hn
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hn
  change 0 ≤ A μ p - 2 * B μ p * B μ p + B μ p ^ 2 at hn
  nlinarith

lemma B_sq_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    (h : DistCov.Indep.FiniteFirstMoment μ) : Integrable (fun p => B μ p ^ 2) m := by
  apply (A_integrable μ h).mono' ((B_meas μ).pow_const 2).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using B_sq_le_A μ p

lemma B_mul_integrable (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : DistCov.Indep.FiniteFirstMoment μ) (hν : DistCov.Indep.FiniteFirstMoment ν) :
    Integrable (fun p => B μ p * B ν p) m := by
  apply ((B_sq_integrable μ hμ).add (B_sq_integrable ν hν)).mono'
    ((B_meas μ).mul (B_meas ν)).aestronglyMeasurable
  filter_upwards [] with p
  change |B μ p * B ν p| ≤ B μ p ^ 2 + B ν p ^ 2
  have hh := sq_nonneg (|B μ p| - |B ν p|)
  rw [abs_mul]
  nlinarith [sq_abs (B μ p), sq_abs (B ν p), mul_nonneg (abs_nonneg (B μ p)) (abs_nonneg (B ν p))]

lemma B_diff_sq_integrable (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : DistCov.Indep.FiniteFirstMoment μ) (hν : DistCov.Indep.FiniteFirstMoment ν) :
    Integrable (fun p => (B μ p - B ν p) ^ 2) m := by
  have he : (fun p => (B μ p - B ν p) ^ 2) =
      (fun p => (B μ p ^ 2 + B ν p ^ 2) - 2 * (B μ p * B ν p)) := by
    funext p; ring
  rw [he]
  exact ((B_sq_integrable μ hμ).add (B_sq_integrable ν hν)).sub
    ((B_mul_integrable μ ν hμ hν).const_mul 2)

lemma B_eq_mass (μ : Measure H) [IsProbabilityMeasure μ] (p : P) :
    B μ p = μ.real {u : H | wEval p.1 u ≤ cGauss * p.2} -
      (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ)) p.2 := by
  have hs : MeasurableSet {u : H | wEval p.1 u ≤ cGauss * p.2} :=
    measurableSet_le (@Measurable.comp H (H × Ω) ℝ _ _ _ (fun q => wEval q.2 q.1)
      (fun u => (u, p.1)) eval_meas (measurable_id.prodMk measurable_const)) measurable_const
  have he : (fun u : H => f u p) =
      (fun u => ({u : H | wEval p.1 u ≤ cGauss * p.2}.indicator (fun _ => (1 : ℝ)) u) -
        (Ici (0 : ℝ)).indicator (fun _ => (1 : ℝ)) p.2) := by
    funext u
    unfold f gaussEmb
    simp only [Set.indicator, Set.mem_Ici, Set.mem_ofPred_eq, div_le_iff₀ c_pos]
    rw [mul_comm p.2 cGauss]
  unfold B
  rw [he, integral_sub ((integrable_const (1 : ℝ)).indicator hs) (integrable_const _),
    integral_indicator_const (1 : ℝ) hs, integral_const]
  simp

lemma baryDiff_eq (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (p : P) :
    baryDiff μ ν p = B μ p - B ν p := by
  rw [B_eq_mass, B_eq_mass]
  unfold baryDiff
  ring

lemma distance_integrable (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : DistCov.Indep.FiniteFirstMoment μ) (hν : DistCov.Indep.FiniteFirstMoment ν) :
    Integrable (fun q : H × H => ‖q.1 - q.2‖) (μ.prod ν) := by
  apply (((norm_integrable μ hμ).comp_fst ν).add ((norm_integrable ν hν).comp_snd μ)).mono'
    ((continuous_fst.sub continuous_snd).norm.measurable.aestronglyMeasurable)
  filter_upwards [] with q
  simpa only [norm_norm, Pi.add_apply, Pi.sub_apply] using norm_sub_le q.1 q.2

lemma diff_kernel_integrable (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : DistCov.Indep.FiniteFirstMoment μ) (hν : DistCov.Indep.FiniteFirstMoment ν) :
    Integrable (fun q : (H × H) × P => (f q.1.1 q.2 - f q.1.2 q.2)^2) ((μ.prod ν).prod m) := by
  have hm : Measurable (fun q : (H × H) × P => (f q.1.1 q.2 - f q.1.2 q.2)^2) := by
    apply Measurable.pow_const
    exact (@Measurable.comp ((H × H) × P) (H × P) ℝ _ _ _ (fun q => f q.1 q.2)
        (fun q => (q.1.1, q.2)) f_meas
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).sub
      (@Measurable.comp ((H × H) × P) (H × P) ℝ _ _ _ (fun q => f q.1 q.2)
        (fun q => (q.1.2, q.2)) f_meas
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun q => (gaussEmb_isometry q.1 q.2).1), ?_⟩
  have he : (fun q : H × H => ∫ p, ‖(f q.1 p - f q.2 p)^2‖ ∂m) =
      (fun q => ‖q.1 - q.2‖) := by
    funext q
    simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact (gaussEmb_isometry q.1 q.2).2.1
  rw [he]
  exact distance_integrable μ ν hμ hν

lemma pair_sq_integral (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (p : P) : ∫ q : H × H, (f q.1 p - f q.2 p)^2 ∂μ.prod ν =
      A μ p + A ν p - 2 * (B μ p * B ν p) := by
  have hi := left_sq_integrable μ p
  have hj := left_sq_integrable ν p
  have hk := (left_integrable μ p).mul_prod (left_integrable ν p)
  have he : (fun q : H × H => (f q.1 p - f q.2 p)^2) =
      (fun q => (f q.1 p ^ 2 + f q.2 p ^ 2) - 2 * (f q.1 p * f q.2 p)) := by
    funext q; ring
  have hi' := hi.comp_fst ν
  have hj' := hj.comp_snd μ
  have hadd : Integrable (fun q : H × H => f q.1 p ^ 2 + f q.2 p ^ 2) (μ.prod ν) := hi'.add hj'
  rw [he, integral_sub hadd (hk.const_mul 2),
    integral_add hi' hj', integral_const_mul,
    integral_fun_fst (μ := μ) (ν := ν) (fun u : H => f u p ^ 2),
    integral_fun_snd (μ := μ) (ν := ν) (fun u : H => f u p ^ 2),
    integral_prod_mul (μ := μ) (ν := ν) (fun u : H => f u p) (fun u : H => f u p)]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, B, A]

lemma energy_eq (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : DistCov.Indep.FiniteFirstMoment μ) (hν : DistCov.Indep.FiniteFirstMoment ν) :
    DistCov.Indep.energy μ ν = (∫ u, ‖u‖ ∂μ) + (∫ u, ‖u‖ ∂ν) -
      2 * ∫ p, B μ p * B ν p ∂m := by
  have hi := diff_kernel_integrable μ ν hμ hν
  have he : DistCov.Indep.energy μ ν =
      ∫ q : H × H, ∫ p, (f q.1 p - f q.2 p)^2 ∂m ∂μ.prod ν := by
    unfold DistCov.Indep.energy
    apply integral_congr_ae
    filter_upwards [] with q
    rw [dist_eq_norm]
    exact (gaussEmb_isometry q.1 q.2).2.1.symm
  rw [he, ← integral_prod _ hi, integral_prod_symm _ hi]
  simp_rw [pair_sq_integral]
  have hadd : Integrable (fun p => A μ p + A ν p) m :=
    (A_integrable μ hμ).add (A_integrable ν hν)
  rw [integral_sub hadd
      ((B_mul_integrable μ ν hμ hν).const_mul 2),
    integral_add (A_integrable μ hμ) (A_integrable ν hν), integral_const_mul,
    A_integral μ hμ, A_integral ν hν]


end DistCovBary
open DistCov.Hilbert DistCovBary

theorem solution (μ₁ μ₂ : Measure DistCov.Indep.L2N) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (h₁ : DistCov.Indep.FiniteFirstMoment μ₁)
    (h₂ : DistCov.Indep.FiniteFirstMoment μ₂) :
    Integrable (fun p => baryDiff μ₁ μ₂ p ^ 2) (rho.prod volume) ∧
    DistCov.Indep.Ddiff μ₁ μ₂ = -2 * ∫ p, baryDiff μ₁ μ₂ p ^ 2 ∂(rho.prod volume) := by
  have he : (fun p => baryDiff μ₁ μ₂ p ^ 2) = (fun p => (B μ₁ p - B μ₂ p)^2) := by
    funext p; rw [baryDiff_eq]
  rw [he]
  refine ⟨B_diff_sq_integrable μ₁ μ₂ h₁ h₂, ?_⟩
  have hex : (fun p => (B μ₁ p - B μ₂ p)^2) =
      (fun p => (B μ₁ p ^ 2 + B μ₂ p ^ 2) - 2 * (B μ₁ p * B μ₂ p)) := by
    funext p; ring
  have hadd : Integrable (fun p => B μ₁ p ^ 2 + B μ₂ p ^ 2) m :=
    (B_sq_integrable μ₁ h₁).add (B_sq_integrable μ₂ h₂)
  rw [hex, integral_sub hadd
      ((B_mul_integrable μ₁ μ₂ h₁ h₂).const_mul 2),
    integral_add (B_sq_integrable μ₁ h₁) (B_sq_integrable μ₂ h₂), integral_const_mul,
    DistCov.Indep.Ddiff, energy_eq μ₁ μ₁ h₁ h₁, energy_eq μ₁ μ₂ h₁ h₂,
    energy_eq μ₂ μ₂ h₂ h₂]
  simp only [pow_two]
  ring

#print axioms solution
