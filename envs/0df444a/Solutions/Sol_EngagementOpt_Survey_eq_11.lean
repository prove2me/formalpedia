-- Prove2me | solution 1 for EngagementOpt.Survey.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:32:30.03616+00:00
-- url     : https://prove2.me/submissions/f2ee41e8-6ebf-4c2d-92ee-88a1d2352eb7

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
theorem solution (β : ℝ) (hβ0 : 0<β) (hβ1 : β≠1) (v W t : ℝ)
    (hv : 0≤v) (hW : 0<W) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => v*(s*β^s/(β^s-1)-1/(β-1))-W*s)
      (v*phi (β^t-1)-W) t ∧
    (0<v → (0<v*phi (β^t-1)-W ↔ W/v<phi (β^t-1))) := by
  refine ⟨SurveyResearch.real_deriv β v W t hβ0 hβ1 ht, ?_⟩
  intro hvp
  constructor
  · intro h
    apply (div_lt_iff₀ hvp).mpr
    nlinarith
  · intro h
    have := (div_lt_iff₀ hvp).mp h
    nlinarith
