-- Prove2me | solution 1 for FairSelling.singleLoss_of_canonical_bundle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:50.224356+00:00
-- url     : https://prove2.me/submissions/ab543efd-eea8-413d-8d88-bd4182fd4517

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_canonical_partitioner_survives
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (a : Fin 3) (hva : ∀ g, 0 ≤ v a g) (hmax : ∀ i, MMS 3 (v i) p ≤ MMS 3 (v a) p)
    {kept : Fin 3 → Finset G} {sold : Finset G} {money : Fin 3 → ℝ} {lo : Fin 3}
    (hcan : IsCanonicalStrict (v a) p ((3 / 4 : ℝ) * MMS 3 (v a) p) kept sold money lo)
    (k : Fin 3) (hk : k ≠ lo) (x : Fin 3)
    (hxacc : (3 / 4 : ℝ) * MMS 3 (v x) p ≤ vbarSum (v x) p (kept k) + money k)
    (hrest : ∀ i, i ≠ x → i = a ∨
      vbarSum (v i) p (kept k) + money k ≤ (3 / 4 : ℝ) * MMS 3 (v i) p) :
    SingleLossConfig v p := by
  classical
  have hcanon := hcan.1
  have hstrict := hcan.2.2
  obtain ⟨hdisj, hsold, hm0, hmsum, hacc, -⟩ := id hcanon
  rcases hstrict k hk with hzero | ⟨hcard1, f, hf, hfp⟩
  · -- a pure bundle: nothing has to be sold
    refine ⟨x, kept k, ∅, 0, Finset.disjoint_empty_right _, le_refl 0, by simp, by simp,
      Or.inr rfl, by rw [hzero] at hxacc; simpa using hxacc, fun i hi => ?_⟩
    rcases hrest i hi with rfl | hrej
    · refine Or.inl ?_
      have := canonical_partitioner_survives (v i) p hva hp hcanon k ∅
        (Finset.empty_subset _) (by simp [hzero])
      simpa [hzero] using this
    · exact Or.inr ⟨by rw [hzero] at hrej; exact hrej, by simp⟩
  · -- a singleton bundle funded by the single sold good `f`
    obtain ⟨hfp, hfprice⟩ := hfp
    have hfnot : f ∉ kept k := fun hmem => (Finset.disjoint_left.mp (hsold k) hf) hmem
    have hsum : ∑ g ∈ ({f} : Finset G), p g = p f := Finset.sum_singleton _ _
    refine ⟨x, kept k, {f}, money k, Finset.disjoint_singleton_right.mpr hfnot, hm0 k,
      by rw [hsum]; exact hfp, by simp, Or.inl (le_of_eq hcard1), hxacc, fun i hi => ?_⟩
    rcases hrest i hi with rfl | hrej
    · exact Or.inl (canonical_partitioner_survives (v i) p hva hp hcanon k {f}
        (Finset.singleton_subset_iff.mpr hf) (by rw [hsum]; exact hfp))
    · refine Or.inr ⟨hrej, fun g hg => ?_⟩
      rw [Finset.mem_singleton.mp hg]
      have := hmax i
      linarith
end FairSelling
