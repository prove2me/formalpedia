-- Prove2me | solution 1 for BranchActualCount.high_height_unit_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:18:40.20019+00:00
-- url     : https://prove2.me/submissions/1d88c262-6938-48d3-9309-c0cb5e892057

import Definitions.Def_RHHeight1000_20261117_P04_v3
open Real Set Filter Complex MeasureTheory
open scoped Topology
section CountPort102
section
open Real Set Filter Complex MeasureTheory
noncomputable instance {T : ℝ} : Fintype (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :=
  (Kadiri.zeroes_rect_univ_positive_height_finite T).fintype
lemma riemannZeta.N_eq_sum (T : ℝ) :
    riemannZeta.N T = ∑ ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset,
      (riemannZeta.order ρ : ℝ) := by
  rw [riemannZeta.N, riemannZeta.zeroes_sum, tsum_fintype, ← Finset.sum_set_coe]
  exact Finset.sum_congr rfl fun _ _ ↦ one_mul _
private lemma riemannZeta.order_nonneg_of_mem_toFinset {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).toFinset) :
    (0 : ℝ) ≤ (riemannZeta.order ρ : ℝ) := by
  exact_mod_cast (Kadiri.riemannZeta_order_pos_positiveHeightZero
    ⟨ρ, Set.mem_toFinset.1 hρ⟩).le
private theorem riemannZeta.zeroes_rect_Ioo_subset {τ t : ℝ} (h : τ ≤ t) :
    riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 τ) ⊆
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 t) :=
  fun _ hz ↦ ⟨hz.1, Set.Ioo_subset_Ioo_right h hz.2.1, hz.2.2⟩
theorem riemannZeta.N_mono : Monotone riemannZeta.N := fun τ t hτt ↦ by
  rw [riemannZeta.N_eq_sum, riemannZeta.N_eq_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hz ↦ Set.mem_toFinset.2 (zeroes_rect_Ioo_subset hτt (Set.mem_toFinset.1 hz)))
    fun _ hρ _ ↦ riemannZeta.order_nonneg_of_mem_toFinset hρ
namespace Zeta.Certificates
end Zeta.Certificates
end
end CountPort102
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
end BranchActualCount

set_option maxHeartbeats 1000000
namespace BranchCountOne
/-- Scalar estimate only. The analytic theta and zero-count hypotheses must be supplied. -/
theorem high_height_arithmetic {T x L a c : ℝ}
    (hT : 1000 ≤ T) (hx : 0 ≤ x) (hxx : x*x = T)
    (hL0 : 0 ≤ L) (hL : L ≤ 2*x)
    (ha : a ≤ 6700*Real.pi+(L+10)*(T+2))
    (hc : c ≤ a/Real.pi+6+L) : c ≤ T*x := by
  have hT0 : 0 ≤ T := by linarith
  have hx30 : 31 ≤ x := by nlinarith
  have hx10 : 30*x ≤ T := by nlinarith [mul_nonneg (show 0 ≤ x-30 by linarith) hx]
  have hp : 0 ≤ (L+10)*(T+2) := by positivity
  have ha' := div_le_div_of_nonneg_right ha Real.pi_pos.le
  have hd := div_le_div_of_nonneg_left hp (by norm_num : (0:ℝ)<3) Real.pi_gt_three.le
  have he : (6700*Real.pi+(L+10)*(T+2))/Real.pi =
      6700+(L+10)*(T+2)/Real.pi := by field_simp
  rw [he] at ha'
  have hc' : c ≤ 6706+(L+10)*(T+2)/3+L := by linarith
  have hprod := mul_nonneg (show 0 ≤ T+2 by linarith) (sub_nonneg.mpr hL)
  have hxprod := mul_le_mul_of_nonneg_left hx30 hT0
  nlinarith
theorem log_shift_bound {T : ℝ} (hT : 1 ≤ T) :
    Real.log (T+3) ≤ 2*Real.sqrt T := by
  have hT0 : 0 ≤ T := by linarith
  have hs := Real.sq_sqrt hT0
  have hs0 := Real.sqrt_nonneg T
  have hs1 : 1 ≤ Real.sqrt T := by nlinarith
  have ht0 : 0 < T+3 := by linarith
  have hroot : 0 < Real.sqrt (T+3) := Real.sqrt_pos.2 ht0
  have hs' := Real.sq_sqrt ht0.le
  have hrle : Real.sqrt (T+3) ≤ Real.sqrt T+1 := by nlinarith
  have hl := Real.log_le_sub_one_of_pos hroot
  rw [Real.log_sqrt ht0.le] at hl
  linarith
#print axioms log_shift_bound
#print axioms high_height_arithmetic
end BranchCountOne

namespace BranchCountOne
/-- Conditional analytic bridge. The phase bound at 1000 is an explicit hypothesis. -/
theorem high_count_of_theta_bound
    (htheta : riemannSiegelTheta 1000 ≤ 6700*Real.pi)
    (T : ℝ) (hT : 1000 ≤ T) :
    riemannZeta.N (T+1) ≤ T*Real.sqrt T := by
  have hT0 : 0 ≤ T := by linarith
  have hL0 : 0 ≤ Real.log (T+3) := Real.log_nonneg (by linarith)
  have hi := BranchActualCount.theta_increment (a:=1000) (b:=T+2)
    (by norm_num) (by linarith)
  have hinc : riemannSiegelTheta (T+2) ≤
      6700*Real.pi+(Real.log (T+3)+10)*(T+2) := by
    have he : T+2+1=T+3 := by ring
    rw [he] at hi
    nlinarith
  have hc := (BranchActualCount.count_one_step (T+1)
    (by nlinarith [Real.pi_lt_four])).1
  have he := BranchActualCount.lehman_error_le (y:=T+2) (U:=T+2)
    (by linarith) le_rfl
  have e1 : T+1+1=T+2 := by ring
  have e2 : T+2+1=T+3 := by ring
  rw [e1] at hc
  rw [e2] at he
  apply high_height_arithmetic hT (Real.sqrt_nonneg T)
    (by nlinarith [Real.sq_sqrt hT0]) hL0 (log_shift_bound (by linarith)) hinc
  linarith
#print axioms high_count_of_theta_bound
end BranchCountOne
namespace BranchCountOne
theorem theta_1000_bound : riemannSiegelTheta 1000 ≤ 6700*Real.pi := by
  have hlog : Real.log (1001:ℝ) ≤ 10 := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<1001)
      (show (1001:ℝ) ≤ 2^10 by norm_num)
    rw [Real.log_pow] at h
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    nlinarith
  have hi := BranchActualCount.theta_increment (a:=7) (b:=1000)
    (by norm_num) (by norm_num)
  have h7 := riemannSiegelTheta_seven_le 0
  norm_num at hi h7
  nlinarith [Real.pi_gt_three]
end BranchCountOne
theorem solution :
    let N : ℝ → ℝ := fun T =>
      ∑' ρ : ↥({s : ℂ | s.re ∈ Set.univ ∧ s.im ∈ Set.Ioo 0 T ∧ s ∈ {z : ℂ | riemannZeta z=0}} : Set ℂ),
        (((meromorphicOrderAt riemannZeta (ρ : ℂ)).untopD 0 : ℤ) : ℝ)
    ∀ T ≥ (1000 : ℝ), N (T+1) ≤ T*Real.sqrt T := by
  dsimp only
  simpa only [riemannZeta.N,riemannZeta.zeroes_sum,riemannZeta.zeroes_rect,
    riemannZeta.zeroes,one_mul,riemannZeta.order] using
    (BranchCountOne.high_count_of_theta_bound BranchCountOne.theta_1000_bound)
#print axioms solution
