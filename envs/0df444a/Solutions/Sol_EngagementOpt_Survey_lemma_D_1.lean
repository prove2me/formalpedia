-- Prove2me | solution 1 for EngagementOpt.Survey.lemma_D_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-18T06:32:26.884986+00:00
-- url     : https://prove2.me/submissions/fe782142-6283-40a3-85cb-d977ae464889

-- Research directed by Alexander Richard Towell (queelius); formalization by OpenAI Codex.
-- Mathematical source: Jon Kleinberg, Sendhil Mullainathan and Manish Raghavan,
-- The Challenge of Understanding What Users Want, arXiv:2202.11776v3.
-- Platform formulation and prior v > W statement repair: mikedeng1.
-- Mathlib contributors supplied the analytic and algebraic foundations.
import Mathlib
import Definitions.Def_EngagementOpt_Survey_phi
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
theorem solution : (∀ x : ℝ, 0<x → 1/2≤phi x) ∧
    (∀ x : ℝ, -1<x → x<0 → phi x≤1/2) := SurveyResearch.phi_bounds
