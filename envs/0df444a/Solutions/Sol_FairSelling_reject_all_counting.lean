-- Prove2me | solution 1 for FairSelling.reject_all_counting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:44.510356+00:00
-- url     : https://prove2.me/submissions/9a3ae674-a295-49c9-8818-311816ef5191

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_four_thr_le_vbarSum_univ
import Theorems.Thm_FairSelling_fin3_sum
import Theorems.Thm_FairSelling_vbarSum_sdiff
import Theorems.Thm_FairSelling_vbarSum_union


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (kept : Fin 3 → Finset G) (money : Fin 3 → ℝ)
    (hdisj : ∀ j k, j ≠ k → Disjoint (kept j) (kept k))
    (k0 k1 k2 : Fin 3) (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h12 : k1 ≠ k2)
    (hrej : ∀ k, vbarSum w p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p + ∑ k, money k ≤
      vbarSum w p (Finset.univ \ (kept k0 ∪ kept k1 ∪ kept k2)) := by
  classical
  have hd01 : Disjoint (kept k0) (kept k1) := hdisj _ _ h01
  have hd02 : Disjoint (kept k0) (kept k2) := hdisj _ _ h02
  have hd12 : Disjoint (kept k1) (kept k2) := hdisj _ _ h12
  have hu : vbarSum w p (kept k0 ∪ kept k1 ∪ kept k2)
      = vbarSum w p (kept k0) + vbarSum w p (kept k1) + vbarSum w p (kept k2) := by
    rw [vbarSum_union w p (Finset.disjoint_union_left.mpr ⟨hd02, hd12⟩), vbarSum_union w p hd01]
  have hsub : kept k0 ∪ kept k1 ∪ kept k2 ⊆ Finset.univ := Finset.subset_univ _
  have hsdiff := vbarSum_sdiff w p hsub
  have htot := four_thr_le_vbarSum_univ w p hw hp
  have hsum : ∑ k, money k = money k0 + money k1 + money k2 := fin3_sum h01 h02 h12 money
  rw [hsdiff, hu]
  have hh0 := hrej k0
  have hh1 := hrej k1
  have hh2 := hrej k2
  rw [hsum]
  linarith
end FairSelling
