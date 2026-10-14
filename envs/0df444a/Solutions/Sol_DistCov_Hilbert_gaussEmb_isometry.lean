-- Prove2me | solution 1 for DistCov.Hilbert.gaussEmb_isometry
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T19:22:39.652104+00:00
-- url     : https://prove2.me/submissions/e3ab8b0f-da23-4fc5-9b8e-749a624199a8

import Theorems.Thm_DistCov_Hilbert_gaussian_series

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace DistCovCrofton
open DistCov.Hilbert
abbrev Ω := ℕ → ℝ
abbrev H := DistCov.Indep.L2N
abbrev P := Ω × ℝ

local instance : IsProbabilityMeasure rho := by
  unfold rho
  infer_instance

lemma c_pos : 0 < cGauss := by
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  unfold cGauss
  apply (integral_pos_iff_support_of_nonneg (fun z => abs_nonneg z) hi).mpr
  have he : Function.support (fun z : ℝ => |z|) = ({0} : Set ℝ)ᶜ := by
    ext z
    simp [Function.support]
  rw [he, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

lemma eval_meas (u : H) : AEMeasurable (fun w => wEval w u) rho := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (fun N => ?_) (gaussian_series u).1
  exact (by fun_prop : Measurable (fun w : Ω => ∑ n ∈ Finset.range N, u n * w n)).aemeasurable

lemma eval_sub (u v : H) :
    (fun w => wEval w u - wEval w v) =ᵐ[rho] (fun w => wEval w (u - v : H)) := by
  filter_upwards [(gaussian_series u).1, (gaussian_series v).1,
    (gaussian_series (u - v)).1] with w hu hv hd
  have hd' : Tendsto
      (fun N => (∑ n ∈ Finset.range N, u n * w n) - ∑ n ∈ Finset.range N, v n * w n)
      atTop (𝓝 (wEval w (u - v : H))) := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using hd
  exact tendsto_nhds_unique (hu.sub hv) hd'

lemma threshold_distance_integrable (u v : H) :
    Integrable (fun w => |wEval w u - wEval w v| / cGauss) rho := by
  apply ((gaussian_series (u - v)).2.2.1.abs.div_const cGauss).congr
  filter_upwards [eval_sub u v] with w hw
  rw [hw]

lemma threshold_distance_integral (u v : H) :
    (∫ w, |wEval w u - wEval w v| / cGauss ∂rho) = ‖u - v‖ := by
  have he : (fun w => |wEval w u - wEval w v| / cGauss) =ᵐ[rho]
      (fun w => |wEval w (u - v : H)| / cGauss) := by
    filter_upwards [eval_sub u v] with w hw
    rw [hw]
  rw [integral_congr_ae he, integral_div, (gaussian_series (u - v)).2.2.2]
  exact mul_div_cancel_left₀ _ (ne_of_gt c_pos)

def ray (a s : ℝ) : ℝ := (Ici a).indicator (fun _ => 1) s

def D (a b s : ℝ) : ℝ := ray a s - ray b s

lemma square_abs (a b s : ℝ) : D a b s ^ 2 = |D a b s| := by
  by_cases ha : a ≤ s <;> by_cases hb : b ≤ s <;>
    norm_num [D, ray, Set.indicator, mem_Ici, ha, hb]

lemma abs_interval (a b : ℝ) :
    (fun s => |D a b s|) = (Ico (min a b) (max a b)).indicator (fun _ => 1) := by
  funext s
  by_cases hab : a ≤ b
  · simp only [min_eq_left hab, max_eq_right hab]
    by_cases ha : a ≤ s <;> by_cases hb : b ≤ s
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb, not_lt.mpr hb]
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb, lt_of_not_ge hb]
    · have hf : False := ha (hab.trans hb)
      exact hf.elim
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb]
  · have hba : b ≤ a := le_of_not_ge hab
    simp only [min_eq_right hba, max_eq_left hba]
    by_cases ha : a ≤ s <;> by_cases hb : b ≤ s
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb, not_lt.mpr ha]
    · have hf : False := hb (hba.trans ha)
      exact hf.elim
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb, lt_of_not_ge ha]
    · simp [D, ray, Set.indicator, mem_Ici, mem_Ico, ha, hb]

lemma abs_integrable (a b : ℝ) : Integrable (fun s => |D a b s|) volume := by
  rw [abs_interval]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (measure_Ico_lt_top.ne))

lemma abs_integral (a b : ℝ) : (∫ s, |D a b s|) = |a - b| := by
  rw [abs_interval]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul, mul_one]
  rw [Real.volume_real_Ico_of_le (min_le_max)]
  exact max_sub_min_eq_abs' a b

lemma ray_meas {A : Ω → ℝ} (hA : AEMeasurable A rho) :
    AEStronglyMeasurable (fun p : P => ray (A p.1) p.2) (rho.prod volume) := by
  have hm : NullMeasurableSet {p : P | A p.1 ≤ p.2} (rho.prod volume) :=
    nullMeasurableSet_le hA.comp_fst measurable_snd.aemeasurable
  have hi := (aestronglyMeasurable_const (b := (1 : ℝ))).indicator₀ hm
  convert hi using 1
  funext p
  simp [ray, Set.indicator, mem_Ici]

lemma emb_meas (u : H) : AEStronglyMeasurable (gaussEmb u) (rho.prod volume) := by
  change AEStronglyMeasurable
    (fun p : P => ray (wEval p.1 u / cGauss) p.2 - ray 0 p.2) (rho.prod volume)
  exact (ray_meas ((eval_meas u).div_const cGauss)).sub
    (ray_meas (A := fun _ => 0) aemeasurable_const)

lemma emb_diff (u v : H) (p : P) :
    gaussEmb u p - gaussEmb v p = D (wEval p.1 u / cGauss) (wEval p.1 v / cGauss) p.2 := by
  unfold gaussEmb D ray
  ring

lemma emb_square_abs (u v : H) (p : P) :
    (gaussEmb u p - gaussEmb v p) ^ 2 = |gaussEmb u p - gaussEmb v p| := by
  rw [emb_diff]
  exact square_abs _ _ _

lemma section_integrable (u v : H) (w : Ω) :
    Integrable (fun s => |gaussEmb u (w, s) - gaussEmb v (w, s)|) volume := by
  simp_rw [emb_diff]
  exact abs_integrable _ _

lemma section_integral (u v : H) (w : Ω) :
    (∫ s, |gaussEmb u (w, s) - gaussEmb v (w, s)|) =
      |wEval w u - wEval w v| / cGauss := by
  simp_rw [emb_diff]
  rw [abs_integral, ← sub_div, abs_div, abs_of_pos c_pos]

lemma emb_abs_integrable (u v : H) :
    Integrable (fun p => |gaussEmb u p - gaussEmb v p|) (rho.prod volume) := by
  have hm : AEStronglyMeasurable (fun p => |gaussEmb u p - gaussEmb v p|) (rho.prod volume) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((emb_meas u).sub (emb_meas v)).norm
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Eventually.of_forall (section_integrable u v)
  · simp_rw [Real.norm_eq_abs, abs_abs, section_integral]
    exact threshold_distance_integrable u v

lemma emb_abs_integral (u v : H) :
    (∫ p, |gaussEmb u p - gaussEmb v p| ∂(rho.prod volume)) = ‖u - v‖ := by
  rw [integral_prod _ (emb_abs_integrable u v)]
  simp_rw [section_integral]
  exact threshold_distance_integral u v

end DistCovCrofton

open DistCov.Hilbert

theorem solution (u u' : DistCov.Indep.L2N) :
    Integrable (fun p => (gaussEmb u p - gaussEmb u' p) ^ 2) (rho.prod volume) ∧
    ∫ p, (gaussEmb u p - gaussEmb u' p) ^ 2 ∂(rho.prod volume) = ‖u - u'‖ ∧
    Integrable (fun p => |gaussEmb u p - gaussEmb u' p|) (rho.prod volume) ∧
    ∫ p, |gaussEmb u p - gaussEmb u' p| ∂(rho.prod volume) = ‖u - u'‖ := by
  have he : (fun p => (gaussEmb u p - gaussEmb u' p) ^ 2) =
      (fun p => |gaussEmb u p - gaussEmb u' p|) :=
    funext (DistCovCrofton.emb_square_abs u u')
  rw [he]
  exact ⟨DistCovCrofton.emb_abs_integrable u u', DistCovCrofton.emb_abs_integral u u',
    DistCovCrofton.emb_abs_integrable u u', DistCovCrofton.emb_abs_integral u u'⟩

#print axioms solution
