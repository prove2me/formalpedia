-- Prove2me | solution 1 for BranchActualCount.eventual_lower_density
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:34:30.10738+00:00
-- url     : https://prove2.me/submissions/0f3ab949-8f3f-4192-9b2b-a030b0a5b59e

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
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
theorem theta_derivative_lower {t : ℝ} (ht : 2≤t) :
    Real.log (t/2)/2-4 ≤ deriv riemannSiegelTheta t := by
  let z : ℂ := 1/4+Complex.I*((t : ℂ)/2)
  have hzre : z.re=1/4 := by simp [z]
  have hzim : z.im=t/2 := by simp [z]
  have hzpos : 0<z.re := by rw [hzre]; norm_num
  have hzn : t/2≤‖z‖ := by simpa only [hzim] using Complex.im_le_norm z
  have hzone : 1≤‖z‖ := by linarith
  have hlog := Real.log_le_log (by linarith : 0<t/2) hzn
  have hraw := Complex.Stirling.norm_digamma_sub_log_le'
    (a:=1/4) (by norm_num) z (by rw [hzre])
  have hcoef : 1/12+3/(2*Real.pi^2*(1/4))≤(2:ℝ) := by
    have hh : 3/(2*Real.pi^2*(1/4))≤(1:ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    linarith
  have hpow : ‖z‖^(-(2:ℤ))≤1 := zpow_le_one_of_nonpos₀ hzone (by norm_num)
  have herror : ‖Complex.digamma z-Complex.log z+(2*z)⁻¹‖≤2 :=
    hraw.trans (by nlinarith [zpow_nonneg (norm_nonneg z) (-(2:ℤ))])
  have hInv : ‖(2*z)⁻¹‖≤1 := by
    rw [norm_inv,norm_mul,Complex.norm_ofNat]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm _).trans herror)).1
  simp only [Complex.add_re,Complex.sub_re,Complex.log_re] at hreal
  have hInvR := Complex.re_le_norm ((2*z)⁻¹)
  have hpi : Real.log Real.pi≤4 := by
    have hh := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_four]
  rw [(hasDerivAt_riemannSiegelTheta (by linarith : 0<t)).deriv]
  change _ ≤ 1/2*(Complex.digamma z).re-1/2*Real.log Real.pi
  linarith
theorem theta_dyadic_lower {T : ℝ} (hT : 4≤T) :
    riemannSiegelTheta (T/2)+(Real.log (T/4)/2-4)*(T/2)
      ≤ riemannSiegelTheta T := by
  have hd (x : ℝ) (hx : x∈Icc (T/2) T) :=
    hasDerivAt_riemannSiegelTheta (by linarith [hx.1] : 0<x)
  have hh := (convex_Icc (T/2) T).mul_sub_le_image_sub_of_le_deriv
    (f:=riemannSiegelTheta) (C:=Real.log (T/4)/2-4)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      have hx' : x∈Icc (T/2) T := interior_subset hx
      have he := theta_derivative_lower (by linarith [hx'.1] : 2≤x)
      have hl := Real.log_le_log (by linarith : 0<T/4)
        (by linarith [hx'.1] : T/4≤x/2)
      linarith)
    (T/2) (left_mem_Icc.mpr (by linarith)) T (right_mem_Icc.mpr (by linarith)) (by linarith)
  linarith
theorem count_dyadic_lower {T : ℝ} (hT : 600≤T) :
    (riemannSiegelTheta (T/2)+(Real.log (T/4)/2-4)*(T/2))/Real.pi
      +1-(5+Real.log (T+2)) ≤ riemannZeta.N (T+1) := by
  have hc := (count_one_step T (by nlinarith [Real.pi_lt_d2])).2
  have ht := theta_dyadic_lower (by linarith : 4≤T)
  have hd := div_le_div_of_nonneg_right ht Real.pi_pos.le
  have he := lehman_error_le (y:=T+1) (U:=T+1) (by linarith) le_rfl
  rw [show T+1+1=T+2 by ring] at he
  linarith
end BranchActualCount
open Real Set Filter Complex MeasureTheory
open scoped Topology
namespace BranchActualCount
theorem count_lower_of_large {T : ℝ} (hT : 1000≤T)
    (hlog : 32≤Real.log T) (hθ : 0≤riemannSiegelTheta ((T-1)/2)) :
    T*Real.log T/(32*Real.pi) ≤ riemannZeta.N T := by
  have hpos : 0<T := by linarith
  have hcnt := count_dyadic_lower (T:=T-1) (by linarith)
  rw [show T-1+1=T by ring,show T-1+2=T+1 by ring] at hcnt
  have hl8 : Real.log 8≤(8:ℝ) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<8)]
  have hlcomp : Real.log T-8≤Real.log ((T-1)/4) := by
    have hh := Real.log_le_log (by positivity : 0<T/8)
      (by linarith : T/8≤(T-1)/4)
    rw [Real.log_div (by linarith : T≠0) (by norm_num : (8:ℝ)≠0)] at hh
    linarith
  have hder : Real.log T/4≤Real.log ((T-1)/4)/2-4 := by linarith
  have hprod : T*Real.log T/16 ≤
      (Real.log ((T-1)/4)/2-4)*((T-1)/2) := by
    have hm := mul_le_mul_of_nonneg_right hder (by linarith : 0≤(T-1)/2)
    nlinarith
  have hln2 : Real.log 2≤(1:ℝ) := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    exact hh
  have hshift : Real.log (T+1)≤Real.log T+1 := by
    have hh := Real.log_le_log (by linarith : 0<T+1) (by linarith : T+1≤T*2)
    rw [Real.log_mul (by linarith : T≠0) (by norm_num : (2:ℝ)≠0)] at hh
    linarith
  have hdiv := div_le_div_of_nonneg_right hprod Real.pi_pos.le
  have hθdiv := div_nonneg hθ Real.pi_pos.le
  have hnorm : T*Real.log T/16/Real.pi = T*Real.log T/(16*Real.pi) := by ring
  rw [hnorm] at hdiv
  rw [add_div] at hcnt
  have hsmall : 6*Real.log T ≤ T*Real.log T/(32*Real.pi) := by
    rw [le_div_iff₀ (by positivity)]
    have hnum : 192*Real.pi≤T := by nlinarith [Real.pi_lt_four]
    have hm := mul_le_mul_of_nonneg_right hnum (by linarith : 0≤Real.log T)
    nlinarith
  have hdouble : T*Real.log T/(16*Real.pi)=2*(T*Real.log T/(32*Real.pi)) := by ring
  rw [hdouble] at hdiv
  linarith
theorem count_lower_eventually :
    ∀ᶠ T : ℝ in atTop, T*Real.log T/(32*Real.pi)≤riemannZeta.N T := by
  have harg : Tendsto (fun T : ℝ => (T-1)/2) atTop atTop := by
    exact (tendsto_atTop_add_const_right atTop (-1) tendsto_id).atTop_div_const (by norm_num)
  have htheta := (tendsto_riemannSiegelTheta_atTop.comp harg).eventually_ge_atTop 0
  have hlogs := Real.tendsto_log_atTop.eventually_ge_atTop 32
  filter_upwards [eventually_ge_atTop (1000:ℝ),hlogs,htheta] with T hT hl ht
  exact count_lower_of_large hT hl ht
end BranchActualCount
theorem solution :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ᶠ T : ℝ in Filter.atTop, T*Real.log T/(32*Real.pi) ≤ N T := by
  dsimp only
  simpa only [riemannZeta.N,riemannZeta.zeroes_sum,riemannZeta.zeroes_rect,
    riemannZeta.zeroes,one_mul,riemannZeta.order] using BranchActualCount.count_lower_eventually
#print axioms solution
