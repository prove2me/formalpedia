-- Prove2me | solution 1 for BCFGJPSSV26.Stable.costF_le_bound_of_degenerate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:04:25.123572+00:00
-- url     : https://prove2.me/submissions/2d0922de-c48a-48bd-aa3e-5dc25cc091fd

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin
public import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
import all Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
public import Theorems.Thm_BCFGJPSSV26_Stable_costF_le_four_opt

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

end Partition

/-- **The degenerate cases** `k = 1` and `opt = 0`. -/
theorem costF_le_bound_of_degenerate {I : Instance} (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ}
    (hN : 201 ≤ N) {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S)
    (h : I.k = 1 ∨ I.opt I.k = 0) : I.costF S ≤ (1.89 + 1000 / N) * I.opt I.k := by
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  rcases h with h1 | h0
  · obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
    have hOne := hO.nonempty hv
    have hSO : (S \ O).card ≤ 24 * N := by
      have := card_le_card (sdiff_subset (s := S) (t := O))
      rw [hS.1, h1] at this
      omega
    have h := hS.2 O hOne (by rw [hO.card]) hSO
    have hδ : (1 : ℝ) / (N * I.k) = 1 / N := by rw [h1]; simp
    rw [hO.cost, hδ] at h
    have hc := Instance.costF_nonneg hv S
    have hNpos : (0 : ℝ) < N := by linarith
    have h1N : 1 / (N : ℝ) ≤ 1 / 201 := one_div_le_one_div_of_le (by norm_num) hN'
    have h1N' : 0 < 1 / (N : ℝ) := by positivity
    have h1000 : (1000 : ℝ) / N = 1000 * (1 / N) := by ring
    rw [h1000]
    nlinarith
  · have h4 := costF_le_four_opt hv hk hN hS
    rw [h0] at h4 ⊢
    linarith

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.costF_le_bound_of_degenerate := @BCFGJPSSV26.Stable.costF_le_bound_of_degenerate
