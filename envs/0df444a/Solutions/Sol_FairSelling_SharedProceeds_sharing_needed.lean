-- Prove2me | solution 1 for FairSelling.SharedProceeds.sharing_needed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:46:37.733018+00:00
-- url     : https://prove2.me/submissions/99c54244-af17-4c7d-83b5-a0691cb3f897

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxSharing
import Theorems.Thm_FairSelling_SharedProceeds_sum_le_three

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.SharedProceeds
namespace FairSelling.SharedProceeds
theorem _root_.solution (o : Outcome (Fin 4) 2) (hvalid : o.Valid sp)
    (hutil : ∀ i, (13 : ℝ) / 3 ≤ util sv o i) :
    (0 : Fin 4) ∈ o.sold ∧ ∀ i, (4 : ℝ) / 3 ≤ o.money i := by
  classical
  obtain ⟨hsk, hkk, hm0, hmsum⟩ := hvalid
  -- the big good must be sold
  have hsold : (0 : Fin 4) ∈ o.sold := by
    by_contra hcon
    -- with `g₀` unsold, no money is available at all
    have hmoney : ∑ i, o.money i ≤ 0 := by
      refine le_trans hmsum ?_
      refine le_of_eq ?_
      refine Finset.sum_eq_zero ?_
      intro g hg
      fin_cases g
      · exact absurd hg hcon
      all_goals norm_num [sp]
    have hm : ∀ i, o.money i = 0 := by
      intro i
      have h1 : (0:ℝ) ≤ ∑ j, o.money j := Finset.sum_nonneg (fun j _ => hm0 j)
      have h2 : o.money i ≤ ∑ j, o.money j :=
        Finset.single_le_sum (fun j _ => hm0 j) (Finset.mem_univ i)
      have := hm0 i
      linarith
    -- at most one agent keeps the big good
    have : ∃ i : Fin 2, (0 : Fin 4) ∉ o.kept i := by
      by_cases h0 : (0 : Fin 4) ∈ o.kept 0
      · refine ⟨1, fun h1 => ?_⟩
        exact Finset.disjoint_left.mp (hkk 0 1 (by decide)) h0 h1
      · exact ⟨0, h0⟩
    obtain ⟨i, hi⟩ := this
    have := hutil i
    unfold util at this
    rw [hm i] at this
    have := sum_le_three hi
    linarith [hutil i, sum_le_three hi]
  refine ⟨hsold, ?_⟩
  intro i
  have hi : (0 : Fin 4) ∉ o.kept i :=
    fun h => Finset.disjoint_left.mp (hsk i) hsold h
  have h1 := hutil i
  unfold util at h1
  have h2 := sum_le_three hi
  linarith
end FairSelling.SharedProceeds
