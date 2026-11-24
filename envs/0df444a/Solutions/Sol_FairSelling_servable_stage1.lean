-- Prove2me | solution 1 for FairSelling.servable_stage1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:05.400817+00:00
-- url     : https://prove2.me/submissions/5ebf9e1b-8b40-4cd9-a590-19c4740d6e3c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
import Theorems.Thm_FairSelling_servable_stage2
import Theorems.Thm_FairSelling_losses_of_stage1
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_servable_extend
import Theorems.Thm_FairSelling_thr_le_thr
import Theorems.Thm_FairSelling_thr_nonneg
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → 0 ≤ D →
      Losses v p T R D → Servable v p (thr v p) T R D := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro T R D hcard hD hL
    by_cases hex : ∃ i ∈ T, ∃ g ∈ R, thr v p i ≤ p g
    · obtain ⟨i, hiT, g, hgR, hprice⟩ := hex
      obtain ⟨j, hjT, hmin⟩ :=
        Finset.exists_min_image T (fun a => MMS n (v a) p) ⟨i, hiT⟩
      have hthr : thr v p j ≤ p g := (thr_le_thr v p (hmin i hiT)).trans hprice
      have hthr0 : 0 ≤ thr v p j := thr_nonneg v p hn hv hp j
      have hcardnew : (T.erase j).card < m := by
        rw [Finset.card_erase_of_mem hjT, hcard]
        have : 0 < m := by rw [← hcard]; exact Finset.card_pos.mpr ⟨j, hjT⟩
        omega
      refine servable_extend v p (thr v p) j hjT ∅ {g} (thr v p j) (Finset.empty_subset _) ?_
        (by simp) hthr0 ?_ ?_
      · simpa using hgR
      · simp [vbarSum]
      · have hR : R \ ((∅ : Finset G) ∪ {g}) = R.erase g := by
          simp [Finset.sdiff_singleton_eq_erase]
        rw [hR]
        simp only [Finset.sum_singleton]
        refine IH _ hcardnew _ _ _ rfl (by linarith) ?_
        exact losses_of_stage1 v p hL hjT hmin hgR hthr hthr0
    · push_neg at hex
      exact servable_stage2 v p hv hp m T R D hcard hD hL (fun a ha e he => hex a ha e he)
end FairSelling
