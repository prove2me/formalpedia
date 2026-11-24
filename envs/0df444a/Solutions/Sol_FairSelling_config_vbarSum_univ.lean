-- Prove2me | solution 1 for FairSelling.config_vbarSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:04:33.567221+00:00
-- url     : https://prove2.me/submissions/dd84f5d3-177c-4b21-bf0f-6fd611985481

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
import Theorems.Thm_FairSelling_cashPrice_none
import Theorems.Thm_FairSelling_cashPrice_some
import Theorems.Thm_FairSelling_cashVal_none
import Theorems.Thm_FairSelling_cashVal_some
import Theorems.Thm_FairSelling_mem_optionGoods
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_vbarSum_sdiff
attribute [local simp] FairSelling.cashPrice_none
attribute [local simp] FairSelling.cashPrice_some
attribute [local simp] FairSelling.cashVal_none
attribute [local simp] FairSelling.cashVal_some
attribute [local simp] FairSelling.mem_optionGoods
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) {A : Fin 3 → Finset G} {s : Finset G} {q : Fin 3 → ℝ}
    {r : ℝ} (hcfg : ConfigN 3 w p r A s q) :
    vbarSum w p Finset.univ = (∑ i, vbarSum w p (A i)) + vbarSum w p s := by
  classical
  obtain ⟨hdisjA, hdisjs, hcover, -⟩ := hcfg
  have hbi : Finset.univ \ s = Finset.univ.biUnion A := by
    ext g
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hg
      have hg' : g ∈ s ∪ Finset.univ.biUnion A := by rw [hcover]; exact Finset.mem_univ g
      rcases Finset.mem_union.mp hg' with h | h
      · exact absurd h hg
      · simpa using h
    · rintro ⟨i, hi⟩ hgs
      exact Finset.disjoint_left.mp (hdisjs i) hgs hi
  have h1 : vbarSum w p (Finset.univ \ s) = ∑ i, vbarSum w p (A i) := by
    rw [hbi, vbarSum, Finset.sum_biUnion (fun i _ j _ hij => hdisjA i j hij)]
    rfl
  have h2 := vbarSum_sdiff w p (Finset.subset_univ s)
  rw [h1] at h2
  linarith
end FairSelling
