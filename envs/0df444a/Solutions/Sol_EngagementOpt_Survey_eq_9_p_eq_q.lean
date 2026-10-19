-- Prove2me | solution 1 for EngagementOpt.Survey.eq_9_p_eq_q
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:32:04.421984+00:00
-- url     : https://prove2.me/submissions/9494abdf-a123-4d56-9097-46e360b17ca5

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
theorem solution (q : ℝ) (hq0 : 0<q) (hq1 : q<1) (t : ℕ) (ht : 1≤t) :
    condMeanTq q q t = ((t:ℝ)+1)/2 := SurveyResearch.mean_equal q hq0 hq1 t ht
