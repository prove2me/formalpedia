-- Prove2me | solution 1 for EngagementOpt.Survey.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:32:00.729465+00:00
-- url     : https://prove2.me/submissions/adfc8cdd-2a19-4d77-b834-e6426e7a03b2

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Mathematical source: Jon Kleinberg, Sendhil Mullainathan and Manish Raghavan,
-- The Challenge of Understanding What Users Want, arXiv:2202.11776v3.
-- Platform formulation and prior v > W statement repair: mikedeng1.
-- Mathlib contributors supplied the analytic and algebraic foundations.
import Mathlib
import Definitions.Def_EngagementOpt_Survey_condUtility
import Definitions.Def_EngagementOpt_Survey_phi
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open EngagementOpt.Survey Finset Filter Topology
namespace SurveyResearch
def gs (r : ℝ) (t : ℕ) : ℝ := ∑ k ∈ Icc 1 t, r^(k-1)
def ws (r : ℝ) (t : ℕ) : ℝ := ∑ k ∈ Icc 1 t, (k:ℝ)*r^(k-1)
lemma gs_succ (r : ℝ) (t : ℕ) : gs r (t+1) = gs r t+r^t := by
  simp [gs,Finset.sum_Icc_succ_top (by omega : 1 ≤ t+1)]
lemma ws_succ (r : ℝ) (t : ℕ) : ws r (t+1) = ws r t+((t:ℝ)+1)*r^t := by
  simp [ws,Finset.sum_Icc_succ_top (by omega : 1 ≤ t+1)]
lemma gs_one (t : ℕ) : gs 1 t = t := by
  induction t with
  | zero => simp [gs]
  | succ t ih => rw [gs_succ,ih]; simp
lemma ws_one (t : ℕ) : ws 1 t = (t:ℝ)*((t:ℝ)+1)/2 := by
  induction t with
  | zero => simp [ws]
  | succ t ih => rw [ws_succ,ih]; push_cast; simp only [one_pow]; ring
lemma gs_identity (r : ℝ) (t : ℕ) : gs r t*(r-1)=r^t-1 := by
  induction t with
  | zero => simp [gs]
  | succ t ih => rw [gs_succ,pow_succ]; nlinarith
lemma ws_identity (r : ℝ) (t : ℕ) :
    ws r t*(r-1)^2=(t:ℝ)*r^(t+1)-((t:ℝ)+1)*r^t+1 := by
  induction t with
  | zero => simp [ws]
  | succ t ih => rw [ws_succ]; push_cast; simp only [pow_succ] at *; nlinarith

lemma joint_factor (p q : ℝ) (hp : p≠0) (t k : ℕ) (hk : k∈Icc 1 t) :
    jointMass p q t k = (p^(t-1)*(1-p)*(1-q))*(q/p)^(k-1) := by
  have hpow : p^(t-1)=p^(t-k)*p^(k-1) := by
    rw [← pow_add]
    congr 1
    have := mem_Icc.mp hk
    omega
  have hk1 := (mem_Icc.mp hk).1
  have hkt := (mem_Icc.mp hk).2
  have hnat : t+1-k-1=t-k := by omega
  simp only [jointMass,geomLaw,if_pos hk1,if_pos (show 1≤t+1-k by omega),hnat]
  rw [hpow,div_pow]
  field_simp

lemma mean_ratio (p q : ℝ) (hp0 : 0<p) (hp1 : p<1) (hq1 : q<1)
    (t : ℕ) : condMeanTq p q t = ws (q/p) t / gs (q/p) t := by
  let c := p^(t-1)*(1-p)*(1-q)
  have hc : c≠0 := ne_of_gt (by dsimp [c]; positivity)
  have hn : (∑ k∈Icc 1 t,(k:ℝ)*jointMass p q t k) = c*ws (q/p) t := by
    rw [ws,mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [joint_factor p q hp0.ne' t k hk]
    dsimp [c]
    ring
  have hd : (∑ k∈Icc 1 t,jointMass p q t k) = c*gs (q/p) t := by
    rw [gs,mul_sum]
    apply sum_congr rfl
    intro k hk
    exact joint_factor p q hp0.ne' t k hk
  rw [condMeanTq,hn,hd,mul_div_mul_left _ _ hc]

lemma mean_equal (p : ℝ) (hp0 : 0<p) (hp1 : p<1) (t : ℕ) (ht : 1≤t) :
    condMeanTq p p t = ((t:ℝ)+1)/2 := by
  rw [mean_ratio p p hp0 hp1 hp1,div_self hp0.ne',ws_one,gs_one]
  have ht0 : (t:ℝ)≠0 := by exact_mod_cast (by omega : t≠0)
  field_simp

lemma mean_unequal (p q : ℝ) (hp0 : 0<p) (hp1 : p<1) (hq0 : 0<q)
    (hq1 : q<1) (hpq : p≠q) (t : ℕ) (ht : 1≤t) :
    condMeanTq p q t = (t:ℝ)*(q/p)^t/((q/p)^t-1)-1/(q/p-1) := by
  let r := q/p
  have hr : 0<r := div_pos hq0 hp0
  have hr1 : r≠1 := by
    intro h
    have : q=p := (div_eq_one_iff_eq hp0.ne').mp h
    exact hpq this.symm
  have hrt : r^t≠1 := by
    rcases lt_or_gt_of_ne hr1 with h|h
    · exact ne_of_lt (pow_lt_one₀ hr.le h (by omega))
    · exact ne_of_gt (one_lt_pow₀ h (by omega))
  have hgs := gs_identity r t
  have hws := ws_identity r t
  have hg : gs r t≠0 := by intro h; rw [h,zero_mul] at hgs; exact hrt (by linarith)
  rw [mean_ratio p q hp0 hp1 hq1]
  change ws r t / gs r t = (t:ℝ)*r^t/(r^t-1)-1/(r-1)
  field_simp
  have hwseq : ws r t*(r-1)^2 = (t:ℝ)*r^t*(r-1)-(r^t-1) := by
    have hh := ws_identity r t
    rw [pow_succ r t] at hh
    nlinarith
  calc
    ws r t*(r^t-1)*(r-1) = gs r t*(ws r t*(r-1)^2) := by rw [← hgs]; ring
    _ = gs r t*((t:ℝ)*r^t*(r-1)-(r^t-1)) := by rw [hwseq]
end SurveyResearch
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open EngagementOpt.Survey Filter Topology
namespace SurveyResearch
def gap (x : ℝ) : ℝ := x^2+2*x-2*(x+1)*Real.log (x+1)
lemma gap_deriv (x : ℝ) (hx : -1<x) :
    HasDerivAt gap (2*x-2*Real.log (x+1)) x := by
  have hlog := ((hasDerivAt_id x).add_const 1).log (by linarith : x+1≠0)
  change HasDerivAt (fun y : ℝ => y^2+2*y-2*(y+1)*Real.log (y+1)) _ x
  have hn : x+1≠0 := by linarith
  have h := (((hasDerivAt_id x).pow 2).add ((hasDerivAt_id x).const_mul 2)).sub
    ((((hasDerivAt_id x).add_const 1).const_mul 2).mul hlog)
  apply h.congr_deriv
  norm_num
  field_simp [show 1+x≠0 by linarith]
  <;> ring
lemma gap_mono : MonotoneOn gap (Set.Ioi (-1)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 2*x-2*Real.log (x+1)) (convex_Ioi (-1))
  · intro x hx
    exact (gap_deriv x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (gap_deriv x (by simpa using hx)).hasDerivWithinAt
  · intro x hx
    have hx' : -1<x := by simpa using hx
    have h := Real.log_le_sub_one_of_pos (by linarith : 0<x+1)
    linarith
lemma phi_gap (x : ℝ) (hx : x≠0) : phi x - 1/2 = gap x/(2*x^2) := by
  unfold phi gap
  field_simp
  <;> ring
lemma phi_bounds :
    (∀ x : ℝ, 0<x → 1/2≤phi x) ∧
    (∀ x : ℝ, -1<x → x<0 → phi x≤1/2) := by
  constructor
  · intro x hx
    have hg := gap_mono (show (0:ℝ)∈Set.Ioi (-1) by norm_num)
      (show x∈Set.Ioi (-1) by change -1<x; linarith) hx.le
    have hg0 : 0≤gap x := by simpa [gap] using hg
    have h := div_nonneg hg0 (by positivity : 0≤2*x^2)
    rw [← phi_gap x hx.ne'] at h
    linarith
  · intro x hx h0
    have hg := gap_mono hx (show (0:ℝ)∈Set.Ioi (-1) by norm_num) h0.le
    have hg0 : gap x≤0 := by simpa [gap] using hg
    have h := div_nonpos_of_nonpos_of_nonneg hg0 (by positivity : 0≤2*x^2)
    rw [← phi_gap x h0.ne] at h
    linarith
end SurveyResearch
namespace SurveyResearch
def realUtility (r v W t : ℝ) : ℝ := v*(t*r^t/(r^t-1)-1/(r-1))-W*t
lemma real_deriv (r v W t : ℝ) (hr : 0<r) (hr1 : r≠1) (ht : 0<t) :
    HasDerivAt (realUtility r v W) (v*phi (r^t-1)-W) t := by
  have hne : r^t-1≠0 := by
    apply sub_ne_zero.mpr
    rcases lt_or_gt_of_ne hr1 with h|h
    · exact (Real.rpow_lt_one hr.le h ht).ne
    · exact (Real.one_lt_rpow h ht).ne'
  have hrp := (hasDerivAt_id t).const_rpow hr
  have h := (((((hasDerivAt_id t).mul hrp).div (hrp.sub_const 1) hne).sub_const
    (1/(r-1))).const_mul v).sub ((hasDerivAt_id t).const_mul W)
  have hlog : Real.log (r^t)=t*Real.log r := Real.log_rpow hr t
  apply h.congr_deriv
  simp only [phi,sub_add_cancel,hlog,id_eq,Pi.mul_apply,mul_one,one_mul]
  field_simp
  <;> ring

lemma real_strictMono (r v W : ℝ) (hr : 1<r) (hv : 0≤v) (hlarge : 2*W<v) :
    StrictMonoOn (realUtility r v W) (Set.Ioi 0) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun t => v*phi (r^t-1)-W) (convex_Ioi 0)
  · intro t ht
    exact (real_deriv r v W t (by linarith) hr.ne' ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (real_deriv r v W t (by linarith) hr.ne' (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : 0<t := by simpa using ht
    have hb := phi_bounds.1 (r^t-1) (sub_pos.mpr (Real.one_lt_rpow hr ht'))
    nlinarith [mul_le_mul_of_nonneg_left hb hv]

lemma real_strictAnti (r v W : ℝ) (hr : 0<r) (hr1 : r<1) (hv : 0≤v)
    (hsmall : v<2*W) : StrictAntiOn (realUtility r v W) (Set.Ioi 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg
    (f' := fun t => v*phi (r^t-1)-W) (convex_Ioi 0)
  · intro t ht
    exact (real_deriv r v W t hr hr1.ne ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (real_deriv r v W t hr hr1.ne (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : 0<t := by simpa using ht
    have hp := Real.rpow_pos_of_pos hr t
    have hb := phi_bounds.2 (r^t-1) (by linarith)
      (sub_neg.mpr (Real.rpow_lt_one hr.le hr1 ht'))
    nlinarith [mul_le_mul_of_nonneg_left hb hv]

lemma utility_real (p q v W : ℝ) (hp0 : 0<p) (hp1 : p<1) (hq0 : 0<q)
    (hq1 : q<1) (hpq : p≠q) (t : ℕ) (ht : 1≤t) :
    condUtility v W p q t = realUtility (q/p) v W t := by
  rw [condUtility,mean_unequal p q hp0 hp1 hq0 hq1 hpq t ht]
  simp only [realUtility,Real.rpow_natCast]

end SurveyResearch
namespace SurveyResearch
def meanFormula (r : ℝ) (t : ℕ) : ℝ := (t:ℝ)*r^t/(r^t-1)-1/(r-1)
lemma mean_limit_low (r : ℝ) (hr : 0<r) (hr1 : r<1) :
    Tendsto (meanFormula r) atTop (𝓝 (-1/(r-1))) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1
  have hmul := tendsto_self_mul_const_pow_of_lt_one hr.le hr1
  have h := (hmul.div (hpow.sub tendsto_const_nhds) (by norm_num : (0:ℝ)-1≠0)).sub
    (tendsto_const_nhds (x := 1/(r-1)))
  change Tendsto (fun t : ℕ => (t:ℝ)*r^t/(r^t-1)-1/(r-1)) atTop _
  simpa [neg_div] using h

lemma mean_limit_high (r : ℝ) (hr : 1<r) :
    Tendsto (fun t : ℕ => meanFormula r t-t) atTop (𝓝 (-1/(r-1))) := by
  have hr0 : 0<r := by linarith
  have hi0 : 0≤r⁻¹ := inv_nonneg.mpr hr0.le
  have hi1 : r⁻¹<1 := inv_lt_one_of_one_lt₀ hr
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hi0 hi1
  have hmul := tendsto_self_mul_const_pow_of_lt_one hi0 hi1
  have h := (hmul.div (tendsto_const_nhds.sub hpow) (by norm_num : (1:ℝ)-0≠0)).sub
    (tendsto_const_nhds (x := 1/(r-1)))
  apply (show Tendsto (fun t : ℕ => (t:ℝ)*(r⁻¹)^t/(1-(r⁻¹)^t)-1/(r-1))
    atTop (𝓝 (-1/(r-1))) by simpa [neg_div] using h).congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  have hrt : r^t≠0 := pow_ne_zero _ hr0.ne'
  have hrt1 : r^t-1≠0 := sub_ne_zero.mpr (ne_of_gt (one_lt_pow₀ hr (by omega)))
  simp only [inv_pow,meanFormula]
  field_simp
  <;> ring

lemma difference_limit (m : ℕ → ℝ) (a L : ℝ)
    (hm : Tendsto (fun t : ℕ => m t-a*t) atTop (𝓝 L)) :
    Tendsto (fun t : ℕ => m (t+1)-m t) atTop (𝓝 a) := by
  have hnext := hm.comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x:=a)).add (hnext.sub hm)
  convert h using 1
  · funext t
    simp only [Function.comp_apply,Nat.cast_add,Nat.cast_one]
    ring
  · simp

lemma utility_difference_limit (p q v W a L : ℝ) (hp0 : 0<p) (hp1 : p<1)
    (hq0 : 0<q) (hq1 : q<1) (hpq : p≠q)
    (hm : Tendsto (fun t : ℕ => meanFormula (q/p) t-a*t) atTop (𝓝 L)) :
    Tendsto (fun t : ℕ => condUtility v W p q (t+1)-condUtility v W p q t)
      atTop (𝓝 (v*a-W)) := by
  have h := ((difference_limit (meanFormula (q/p)) a L hm).const_mul v).sub
    (tendsto_const_nhds (x:=W))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [condUtility,condUtility,mean_unequal p q hp0 hp1 hq0 hq1 hpq t ht,
    mean_unequal p q hp0 hp1 hq0 hq1 hpq (t+1) (by omega)]
  simp only [meanFormula,Nat.cast_add,Nat.cast_one]
  ring
end SurveyResearch
open SurveyResearch
theorem solution (p q v W : ℝ) (hp0 : 0<p) (hp1 : p<1) (hq0 : 0<q) (hq1 : q<1)
    (hv : 0≤v) (hW : 0<W) :
    (q=p → ((∀ t : ℕ, 1≤t → condUtility v W p q t < condUtility v W p q (t+1)) ↔ 2*W<v)) ∧
    (p<q → 2*W<v → ∀ t : ℕ, 1≤t → condUtility v W p q t < condUtility v W p q (t+1)) ∧
    (p<q → W<v → ∃ t₀ : ℕ, ∀ t : ℕ, t₀<t → condUtility v W p q t < condUtility v W p q (t+1)) ∧
    (q<p → v<2*W → ∀ t : ℕ, 1≤t → condUtility v W p q (t+1) < condUtility v W p q t) ∧
    (q<p → ∃ t₀ : ℕ, ∀ t : ℕ, t₀<t → condUtility v W p q (t+1) < condUtility v W p q t) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro heq
    subst q
    constructor
    · intro h
      have h12 := h 1 (by omega)
      rw [condUtility,condUtility,mean_equal p hp0 hp1 1 (by omega),
        mean_equal p hp0 hp1 2 (by omega)] at h12
      norm_num at h12
      linarith
    · intro h t ht
      rw [condUtility,condUtility,mean_equal p hp0 hp1 t ht,
        mean_equal p hp0 hp1 (t+1) (by omega)]
      push_cast
      linarith
  · intro hpq hlarge t ht
    rw [utility_real p q v W hp0 hp1 hq0 hq1 hpq.ne t ht,
      utility_real p q v W hp0 hp1 hq0 hq1 hpq.ne (t+1) (by omega)]
    exact real_strictMono (q/p) v W ((one_lt_div hp0).mpr hpq) hv hlarge
      (by change (0:ℝ)<t; exact_mod_cast (by omega : 0<t))
      (by change (0:ℝ)<(t+1:ℕ); positivity) (by exact_mod_cast Nat.lt_succ_self t)
  · intro hpq hvW
    have hr : 1<q/p := (one_lt_div hp0).mpr hpq
    have hm : Tendsto (fun t : ℕ => meanFormula (q/p) t-1*t) atTop (𝓝 (-1/(q/p-1))) := by
      simpa using mean_limit_high (q/p) hr
    have hd := utility_difference_limit p q v W 1 (-1/(q/p-1)) hp0 hp1 hq0 hq1 hpq.ne hm
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hd).1 0 (by linarith : 0<v*1-W))
    refine ⟨N,fun t ht => ?_⟩
    have := hN t ht.le
    linarith
  · intro hqp hsmall t ht
    rw [utility_real p q v W hp0 hp1 hq0 hq1 hqp.ne' t ht,
      utility_real p q v W hp0 hp1 hq0 hq1 hqp.ne' (t+1) (by omega)]
    exact real_strictAnti (q/p) v W (div_pos hq0 hp0) ((div_lt_one hp0).mpr hqp) hv hsmall
      (by change (0:ℝ)<t; exact_mod_cast (by omega : 0<t))
      (by change (0:ℝ)<(t+1:ℕ); positivity) (by exact_mod_cast Nat.lt_succ_self t)
  · intro hqp
    have hm : Tendsto (fun t : ℕ => meanFormula (q/p) t-0*t) atTop (𝓝 (-1/(q/p-1))) := by
      simpa using mean_limit_low (q/p) (div_pos hq0 hp0) ((div_lt_one hp0).mpr hqp)
    have hd := utility_difference_limit p q v W 0 (-1/(q/p-1)) hp0 hp1 hq0 hq1 hqp.ne' hm
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hd).2 0 (by linarith : v*0-W<0))
    refine ⟨N,fun t ht => ?_⟩
    have := hN t ht.le
    linarith
