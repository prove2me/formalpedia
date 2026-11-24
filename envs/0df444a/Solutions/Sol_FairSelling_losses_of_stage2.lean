-- Prove2me | solution 1 for FairSelling.losses_of_stage2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:11:29.559173+00:00
-- url     : https://prove2.me/submissions/c03f7699-9117-4461-a297-35d4a9f07f42

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Theorems.Thm_FairSelling_losses_extend
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    (hstage1 : ∀ a ∈ T, ∀ e ∈ R, p e < thr v p a)
    {i : Fin n} (hi : i ∈ T) {g : G} (hg : g ∈ R) :
    Losses v p (T.erase i) (R.erase g) D := by
  classical
  have key := losses_extend v p hL hi {g} ∅ 0 (by simpa using hg) (Finset.empty_subset _)
    (by simp) le_rfl ?_
  · have hR : R \ (({g} : Finset G) ∪ ∅) = R.erase g := by
      simp [Finset.sdiff_singleton_eq_erase]
    rw [hR] at key
    simpa using key
  · intro b hb Eb
    by_cases hgS : g ∈ Eb.sell
    · refine Or.inr (Or.inl ⟨?_, ?_⟩)
      · have h1 : v b g ≤ p g := Eb.sell_price g hgS
        have h2 : p g < thr v p b := hstage1 b (Finset.mem_of_mem_erase hb) g hg
        have : vbarSum (v b) p {g} = p g := by
          simp [vbarSum, vbar, max_eq_left h1]
        rw [this]
        linarith
      · intro f hf; simp at hf
    · exact Or.inl ⟨g, hgS, Or.inl ⟨rfl, rfl, rfl⟩⟩
end FairSelling
