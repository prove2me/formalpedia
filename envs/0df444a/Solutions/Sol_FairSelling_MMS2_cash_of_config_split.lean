-- Prove2me | solution 1 for FairSelling.MMS2_cash_of_config_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:02:49.244178+00:00
-- url     : https://prove2.me/submissions/8c38fba4-9316-47ae-952f-57aa1a178508

import Mathlib
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_ConfigSplit
import Theorems.Thm_FairSelling_MMS2_cash_of_two_bundles_sell


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ} {r : ℝ}
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hcfg : ConfigN 3 w p r A s q) (X : Finset G) (c τ : ℝ) (hc : 0 ≤ c)
    {j j' j'' : Fin 3} (h1 : j ≠ j') (h2 : j ≠ j'')
    (hbudget : max 0 (τ - vbarSum w p (A j \ X)) + max 0 (τ - vbarSum w p ((A j' ∪ A j'') \ X))
      ≤ c + ∑ g ∈ s \ X, p g) :
    τ ≤ MMS 2 (cashVal (Finset.univ \ X) w) (cashPrice (Finset.univ \ X) p c) := by
  classical
  obtain ⟨hdisjA, hdisjs, -⟩ := hcfg
  refine MMS2_cash_of_two_bundles_sell w p hw hp (Finset.univ \ X) (A j \ X)
    ((A j' ∪ A j'') \ X) (s \ X) c
    (max 0 (τ - vbarSum w p (A j \ X))) (max 0 (τ - vbarSum w p ((A j' ∪ A j'') \ X))) τ
    ?_ ?_ ?_ ?_ ?_ ?_ hc (le_max_left _ _) (le_max_left _ _) hbudget ?_ ?_
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxj := (Finset.mem_sdiff.mp hx).1
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx').1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjA j j' h1)) hxj h
    · exact (Finset.disjoint_left.mp (hdisjA j j'' h2)) hxj h
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    exact (Finset.disjoint_left.mp (hdisjs j)) (Finset.mem_sdiff.mp hx').1
      (Finset.mem_sdiff.mp hx).1
  · refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
    have hxs := (Finset.mem_sdiff.mp hx').1
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1 with h | h
    · exact (Finset.disjoint_left.mp (hdisjs j')) hxs h
    · exact (Finset.disjoint_left.mp (hdisjs j'')) hxs h
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · exact Finset.sdiff_subset_sdiff (Finset.subset_univ _) (le_refl X)
  · rcases le_or_gt τ (vbarSum w p (A j \ X)) with h | h
    · linarith [le_max_left (0 : ℝ) (τ - vbarSum w p (A j \ X))]
    · rw [max_eq_right (by linarith)]; linarith
  · rcases le_or_gt τ (vbarSum w p ((A j' ∪ A j'') \ X)) with h | h
    · linarith [le_max_left (0 : ℝ) (τ - vbarSum w p ((A j' ∪ A j'') \ X))]
    · rw [max_eq_right (by linarith)]; linarith
end FairSelling
