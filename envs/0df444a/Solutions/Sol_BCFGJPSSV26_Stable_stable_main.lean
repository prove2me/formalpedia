-- Prove2me | solution 1 for BCFGJPSSV26.Stable.stable_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:25:33.31482+00:00
-- url     : https://prove2.me/submissions/29c56939-a7e0-4883-a7c1-560309ae5e39

module

public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
public import Definitions.Def_BCFGJPSSV26_Combine
public import Theorems.Thm_BCFGJPSSV26_Stable_alg_valid
public import Theorems.Thm_BCFGJPSSV26_Stable_exists_runsInTime
public import Theorems.Thm_BCFGJPSSV26_Stable_success_prob

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Encoding

/-- **Theorem 1.1 of Part II.** -/
theorem stable_main : Combine.Thm13 := by
  obtain ⟨a, hrun, hbud⟩ := exists_runsInTime
  refine ⟨algQ, a, 2, 1000, hrun, fun I hv hk L ε ↦
    ⟨fun r ↦ alg_valid (prmOf ε) hv hk L r, fun hε _ β hβ hst hL ↦ ?_⟩⟩
  set P := prmOf ε
  have hNpos : (0 : ℝ) < P.N := P.N_pos'
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  -- the accuracy `1/N`
  have h1N : 1 / (P.N : ℝ) ≤ ε := by
    have h : ((1 / ε : ℚ) : ℝ) < ((accN ε : ℚ) : ℝ) := Rat.cast_lt.2 (inv_lt_accN hε)
    push_cast at h
    exact ((one_div_lt hε' hNpos).1 h).le
  -- the probability
  have hT : Par.coinLen P.N I L ≤ stableTimeOf a 2 ((I, L), ε) :=
    (Par.coinLen_le_budget hk P.N_pos).trans (hbud ((I, L), ε))
  have h := success_prob P hv hk hβ hst hL hT
  have hopt := Instance.opt_nonneg' hv I.k
  refine le_trans (by linarith) (h.trans (Combine.coinProb_mono fun r hr ↦ ?_))
  rw [algQ_eq]
  have hne := Instance.centers_nonempty (alg_valid P hv hk L r).1.1 (alg_valid P hv hk L r).1.2.2
  rw [← Instance.costF_eq_cost hne]
  refine hr.trans ?_
  unfold bound
  refine mul_le_mul_of_nonneg_right ?_ hopt
  have : (1000 : ℝ) / P.N ≤ 1000 * ε := by
    rw [show (1000 : ℝ) / P.N = 1000 * (1 / P.N) by ring]
    exact mul_le_mul_of_nonneg_left h1N (by norm_num)
  linarith

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.stable_main := @BCFGJPSSV26.Stable.stable_main
