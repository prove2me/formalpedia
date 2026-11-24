-- Prove2me | solution 1 for FairSelling.config_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:30:01.905818+00:00
-- url     : https://prove2.me/submissions/e59e92f4-3441-442e-9a1c-d31f000c033f

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Theorems.Thm_FairSelling_vbarSum_union
import Theorems.Thm_FairSelling_biU_two

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (M : ℝ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (h : Config w p M A s q) : 2 * M ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g := by
  obtain ⟨hdisjA, hdisjs, hcover, hq0, hsat, hge⟩ := h
  rw [biU_two A] at hcover
  have hAunion : A 0 ∪ A 1 = Finset.univ \ s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro (hx | hx)
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 0) hxs hx
      · exact fun hxs => Finset.disjoint_left.mp (hdisjs 1) hxs hx
    · intro hxs
      have hmem : x ∈ s ∪ (A 0 ∪ A 1) := hcover ▸ Finset.mem_univ x
      rcases Finset.mem_union.mp hmem with h' | h'
      · exact absurd h' hxs
      · exact Finset.mem_union.mp h'
  have hvbar : vbarSum w p (A 0 ∪ A 1) = vbarSum w p (A 0) + vbarSum w p (A 1) :=
    vbarSum_union w p (hdisjA 0 1 (by decide))
  have hqsum : q 0 + q 1 = ∑ g ∈ s, p g := by rw [← Fin.sum_univ_two q]; exact hsat
  rw [← hAunion, hvbar]
  linarith [hge 0, hge 1, hqsum]
end FairSelling
