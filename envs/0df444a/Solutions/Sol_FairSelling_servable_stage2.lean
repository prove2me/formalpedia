-- Prove2me | solution 1 for FairSelling.servable_stage2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:24:33.836706+00:00
-- url     : https://prove2.me/submissions/e861921c-9492-4f5c-9d76-2d1725e6ca04

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
import Theorems.Thm_FairSelling_servable_of_inv
import Theorems.Thm_FairSelling_losses_of_stage2
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_servable_extend
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → (∀ a ∈ T, ∀ e ∈ R, p e < thr v p a) →
      Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hD hL hstage1
    by_cases hex : ∃ i ∈ T, ∃ g ∈ R, thr v p i ≤ v i g
    · obtain ⟨i, hiT, g, hgR, hval⟩ := hex
      have hcardnew : (T.erase i).card < m := by
        rw [Finset.card_erase_of_mem hiT, hcard]
        have : 0 < m := by rw [← hcard]; exact Finset.card_pos.mpr ⟨i, hiT⟩
        omega
      refine servable_extend v p (thr v p) i hiT {g} ∅ 0 ?_ (Finset.empty_subset _)
        (by simp) le_rfl ?_ ?_
      · simpa using hgR
      · have : vbarSum (v i) p {g} = vbar (v i) p g := by simp [vbarSum]
        rw [this, add_zero]
        exact hval.trans (le_max_right _ _)
      · have hR : R \ ({g} ∪ (∅ : Finset G)) = R.erase g := by
          simp [Finset.sdiff_singleton_eq_erase]
        rw [hR]
        simp only [Finset.sum_empty, add_zero, sub_zero]
        refine IH _ hcardnew _ _ _ rfl hD ?_ ?_
        · exact losses_of_stage2 v p hL hstage1 hiT hgR
        · intro a ha e he
          exact hstage1 a (Finset.mem_of_mem_erase ha) e (Finset.mem_of_mem_erase he)
    · push_neg at hex
      refine servable_of_inv v p hv hp m T R D hcard ⟨hD, hL, ?_⟩
      intro a haT g hgR
      have h1 : p g < thr v p a := hstage1 a haT g hgR
      have h2 : v a g < thr v p a := hex a haT g hgR
      simp only [vbar]
      exact max_lt h1 h2
end FairSelling
