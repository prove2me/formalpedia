-- Prove2me | solution 2 for FairChores.SEF1_of_SEFX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:52:58.884849+00:00
-- url     : https://prove2.me/submissions/40911189-f8b3-4edc-b656-f5de3cf01831

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresEnvy
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbarSum_nonneg
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable {c : Fin n → T → ℝ} {p : T → ℝ} {o : Outcome T n}
namespace FairChores
theorem _root_.solution (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t)
    (hvalid : o.Valid p) (h : SEFX c p o) : SEF1 c p o := by
  intro i j
  refine ⟨(h i j).1, fun hi => ?_⟩
  rcases (h i j).2 hi with hEF | hall
  · exact Or.inl hEF
  · rcases Finset.eq_empty_or_nonempty (o.kept i) with hemp | ⟨t, ht⟩
    · refine Or.inl ?_
      have h1 : 0 ≤ cbarSum (c i) p (o.kept j) := cbarSum_nonneg (hc i) hp _
      have h2 := hvalid.2.2.2.1 j
      rw [hemp, hi, cbarSum_empty]
      linarith
    · exact Or.inr ⟨t, ht, hall t ht⟩
end FairChores
