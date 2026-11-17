-- Prove2me | solution 1 for BranchActualCount.unit_window_bound
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:34:19.447701+00:00
-- url     : https://prove2.me/submissions/5a683fcd-aa0a-4195-a7dd-3f5351e357e8

import Definitions.Def_RHCount_XiProduct_20261116_v1
import Definitions.Def_RHCount_ZeroCounting_20261116_v1
import Definitions.Def_RHCount_ArgumentBounds_20261116_v1
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
theorem count_one_step (T : ℝ) (hT : 168 * Real.pi < T) :
    riemannZeta.N T ≤ riemannSiegelTheta (T+1)/Real.pi + 1 +
      (5 + 0.128 * Real.log ((T+1)/(2*Real.pi))) ∧
    riemannSiegelTheta T/Real.pi + 1 -
      (5 + 0.128 * Real.log ((T+1)/(2*Real.pi))) ≤ riemannZeta.N (T+1) := by
  have hT0 : 0<T := lt_trans (by positivity) hT
  have hT7 : 7≤T := by nlinarith [Real.pi_gt_three]
  have hTle : T≤T+1 := by linarith
  have hf : ∀ᵐ t ∂(volume.restrict (Icc T (T+1))),
      riemannZeta.N t = riemannSiegelTheta t/Real.pi+1+argZeta t := by
    filter_upwards [(finite_setOf_riemannZeta_zero_ray_Icc hT0 hTle).countable.ae_notMem
      (volume.restrict (Icc T (T+1))), ae_restrict_mem measurableSet_Icc] with t ht ht'
    push Not at ht
    have ht_good := mt ht (by simpa using ht')
    push Not at ht_good
    exact riemannZeta.N_eq_of_forall_re_mem_Ico (by linarith [ht'.1])
      (fun σ hσ => ht_good σ (by simpa using hσ.1))
  have hLow : (fun _ : ℝ => riemannZeta.N T - riemannSiegelTheta (T+1)/Real.pi - 1)
      ≤ᵐ[volume.restrict (Icc T (T+1))] argZeta := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hn := riemannZeta.N_mono hmem.1
    have hθ := strictMonoOn_riemannSiegelTheta_gramDomain.monotoneOn
      (show t∈gramDomain from by change 7≤t; linarith [hmem.1])
      (show T+1∈gramDomain from by change 7≤T+1; linarith) hmem.2
    have hθd := div_le_div_of_nonneg_right hθ Real.pi_pos.le
    linarith
  have hUp : argZeta ≤ᵐ[volume.restrict (Icc T (T+1))]
      (fun _ : ℝ => riemannZeta.N (T+1) - riemannSiegelTheta T/Real.pi - 1) := by
    filter_upwards [hf, ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hn := riemannZeta.N_mono hmem.2
    have hθ := strictMonoOn_riemannSiegelTheta_gramDomain.monotoneOn
      (show T∈gramDomain from hT7)
      (show t∈gramDomain from by change 7≤t; linarith [hmem.1]) hmem.1
    have hθd := div_le_div_of_nonneg_right hθ Real.pi_pos.le
    linarith
  have hint := intervalIntegrable_argZeta hT0 hTle
  have hlo := intervalIntegral.integral_mono_ae_restrict hTle intervalIntegrable_const hint hLow
  have hup := intervalIntegral.integral_mono_ae_restrict hTle hint intervalIntegrable_const hUp
  have hb := abs_le.mp (norm_integral_argZeta_le_five_unconditional hT (by linarith : T<T+1))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hlo hup
  constructor <;> nlinarith [hb.1, hb.2]
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
theorem theta_derivative_bound {t U : ℝ} (ht : 2≤t) (hU : t≤U) :
    ‖deriv riemannSiegelTheta t‖ ≤ Real.log (U+1)+10 := by
  let z : ℂ := 1/4+Complex.I*((t : ℂ)/2)
  have hzre : z.re=1/4 := by simp [z]
  have hzim : z.im=t/2 := by simp [z]
  have hzpos : 0<z.re := by rw [hzre]; norm_num
  have hzone : 1≤‖z‖ := by
    have hh := Complex.im_le_norm z
    rw [hzim] at hh
    linarith
  have hzupper : ‖z‖≤U+1 := by
    have hh := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre,hzim,abs_of_nonneg (by norm_num : (0:ℝ)≤1/4),
      abs_of_nonneg (by linarith : 0≤t/2)] at hh
    linarith
  have hlog := Real.log_le_log (by linarith : 0<‖z‖) hzupper
  have hpsi := Complex.norm_digamma_le hzpos hzone
  have hpi : 0≤Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpib : Real.log Real.pi≤4 := by
    have hh := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  have hu0 : 0≤Real.log (U+1) := Real.log_nonneg (by linarith)
  have hpr := Complex.abs_re_le_norm (Complex.digamma z)
  rw [(hasDerivAt_riemannSiegelTheta (by linarith : 0<t)).deriv,Real.norm_eq_abs]
  change |1/2*(Complex.digamma z).re-1/2*Real.log Real.pi|≤_
  calc
    _ ≤ |1/2*(Complex.digamma z).re|+|1/2*Real.log Real.pi| := abs_sub _ _
    _ = 1/2*|(Complex.digamma z).re|+1/2*Real.log Real.pi := by
      rw [abs_mul,abs_mul,abs_of_nonneg hpi]
      norm_num
    _ ≤ Real.log (U+1)+10 := by nlinarith [Real.pi_lt_four]
theorem theta_increment {a b : ℝ} (ha : 2≤a) (hab : a≤b) :
    riemannSiegelTheta b-riemannSiegelTheta a ≤
      (Real.log (b+1)+10)*(b-a) := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=riemannSiegelTheta) (s:=Icc a b)
    (fun x hx => (hasDerivAt_riemannSiegelTheta (by linarith [hx.1] : 0<x)).differentiableAt)
    (fun x hx => theta_derivative_bound (by linarith [hx.1]) hx.2)
    (convex_Icc a b) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hab)] at hh
  exact (le_abs_self _).trans hh
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
theorem lehman_error_le {y U : ℝ} (hy : 0<y) (hyU : y≤U) :
    5+0.128*Real.log (y/(2*Real.pi)) ≤ 5+Real.log (U+1) := by
  have hU : 0<U := hy.trans_le hyU
  have hrat : y/(2*Real.pi)≤U+1 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hl := Real.log_le_log (by positivity : 0<y/(2*Real.pi)) hrat
  have hp := Real.log_nonneg (by linarith : 1≤U+1)
  linarith
theorem count_unit_window {T : ℝ} (hT : 600≤T) :
    riemannZeta.N (T+1)-riemannZeta.N T ≤ 50*Real.log (T+3) := by
  have hleft : 168*Real.pi<T-1 := by nlinarith [Real.pi_lt_d2]
  have hright : 168*Real.pi<T+1 := by linarith
  have hl := (count_one_step (T-1) hleft).2
  have hr := (count_one_step (T+1) hright).1
  have heql : T-1+1=T := by ring
  have heqr : T+1+1=T+2 := by ring
  rw [heql] at hl
  rw [heqr] at hr
  have htheta := theta_increment (a:=T-1) (b:=T+2) (by linarith) (by linarith)
  have hu : T+2+1=T+3 := by ring
  have hd : T+2-(T-1)=3 := by ring
  rw [hu,hd] at htheta
  have hL : 1≤Real.log (T+3) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have he1 := lehman_error_le (y:=T) (U:=T+2) (by linarith) (by linarith)
  have he2 := lehman_error_le (y:=T+2) (U:=T+2) (by linarith) le_rfl
  rw [hu] at he1 he2
  have hthetaD : (riemannSiegelTheta (T+2)-riemannSiegelTheta (T-1))/Real.pi
      ≤ 3*(Real.log (T+3)+10) := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  rw [sub_div] at hthetaD
  linarith
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
end BranchActualCount
theorem solution :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ T ≥ (600 : ℝ), N (T+1)-N T ≤ 50*Real.log (T+3) := by
  dsimp only
  simpa only [riemannZeta.N,riemannZeta.zeroes_sum,riemannZeta.zeroes_rect,
    riemannZeta.zeroes,one_mul,riemannZeta.order] using (fun T hT => BranchActualCount.count_unit_window (T:=T) hT)
#print axioms solution
