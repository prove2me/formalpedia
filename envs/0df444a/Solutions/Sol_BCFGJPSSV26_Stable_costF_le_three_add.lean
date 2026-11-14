-- Prove2me | solution 1 for BCFGJPSSV26.Stable.costF_le_three_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:02:53.939196+00:00
-- url     : https://prove2.me/submissions/44a72b09-1469-40b9-9ca6-698eb474288d

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
import all Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Theorems.Thm_BCFGJPSSV26_Stable_refined_ls

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- **Local search is a `(3 + 100/N)`-approximation.** -/
theorem costF_le_three_add (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ (3 + 100 / N) * I.opt I.k := by
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
  have hOne := hO.nonempty hv
  have hSne : S.Nonempty := by
    rw [← card_pos, hS.1]
    exact hv.one_le_k
  set μB : Fin I.n → Fin I.m := fun j ↦ I.near O hOne (.inl j)
  set μA : Fin I.n → Fin I.m := fun j ↦ I.near S hSne (.inr (μB j))
  have hsize : O.card + ((univ : Finset (Fin I.n))ᶜ.image μA).card ≤ I.k := by
    simp [hO.card]
  have h := refined_ls hv (by omega) hS (μA := μA) (μB := μB)
    (fun j ↦ Instance.near_mem hSne _) (fun j ↦ Instance.near_mem hOne _) hsize
    (crossFree_near_near hSne hOne)
  have hB : I.costMap μB univ = I.opt I.k := by
    rw [← hO.cost]
    exact sum_congr rfl fun j _ ↦ Instance.dd_near hOne _
  have hA : I.costMap μA univ ≤ I.costF S + 2 * I.opt I.k := by
    rw [← hO.cost]
    exact costMap_near_near_le hv hSne hOne
  rw [hB, Instance.costOn_univ] at h
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set t : ℝ := 10 / N with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 10 / 201 := by
    rw [ht]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have h100 : (100 : ℝ) / N = 10 * t := by rw [ht]; ring
  rw [h100]
  have hc := Instance.costF_nonneg hv S
  have h1 : I.costF S ≤ 3 * I.opt I.k + t * (I.costF S + 3 * I.opt I.k) := by
    have := mul_le_mul_of_nonneg_left (add_le_add_right hA (I.opt I.k)) ht0.le
    nlinarith
  have h2 : (1 - t) * I.costF S ≤ (1 - t) * ((3 + 10 * t) * I.opt I.k) := by
    nlinarith [mul_nonneg (mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 4 - 10 * t)) hopt]
  exact le_of_mul_le_mul_left h2 (by linarith)

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.costF_le_three_add := @BCFGJPSSV26.Stable.costF_le_three_add
