-- Prove2me | solution 1 for FairSelling.eventCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:35.588805+00:00
-- url     : https://prove2.me/submissions/3b73ea24-3b43-4eb2-b17e-59b47b2b27a3

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_vbar_le_of_mem_part
import Theorems.Thm_FairSelling_eventCost_le_aux
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (hμ : 0 ≤ μ) {t : ℝ} (ht : t = (2 / 3) * μ)
    {Ea Fa : Finset G} (hEF : Disjoint Ea Fa) {c : ℝ}
    (hloss : LossOK w p E.sell μ t Ea Fa c) :
    eventCost E Ea Fa c ≤ μ := by
  classical
  have haux := eventCost_le_aux E hp Ea Fa hEF c
  have hvbar0 : ∀ g, 0 ≤ vbar w p g := fun g => le_trans (hp g) (le_max_left _ _)
  -- a good of the sell set contributes nothing to the sold-goods correction
  have hsell_zero : ∀ g ∈ E.sell, vbar w p g - p g = 0 := by
    intro g hg
    simp only [vbar, max_eq_left (E.sell_price g hg), sub_self]
  rcases hloss with h1 | h2 | h3 | h4
  · -- `ℓ₁`
    obtain ⟨e, heS, hcase⟩ := h1
    rcases hcase with ⟨hEa, hFa, hc⟩ | ⟨hEa, hFa, hc⟩
    · -- the good is handed over
      subst hEa; subst hFa; subst hc
      have : vbarSum w p {e} + (∑ g ∈ (∅ : Finset G), (vbar w p g - p g)) + 0 = vbar w p e := by
        simp [vbarSum]
      rw [this] at haux
      by_cases hmem : ∃ j, e ∈ E.part j
      · obtain ⟨j, hj⟩ := hmem
        exact haux.trans (vbar_le_of_mem_part E hp hj)
      · push_neg at hmem
        -- the good belongs to no part and is not sold: it costs nothing
        have hzero : eventCost E {e} ∅ 0 = 0 := by
          simp only [eventCost, Finset.union_empty, Finset.sum_empty, add_zero, sub_zero]
          have hp1 : ∀ j, E.part j ∩ ({e} : Finset G) = ∅ :=
            fun j => Finset.inter_singleton_of_notMem (hmem j)
          have hp2 : E.sell ∩ ({e} : Finset G) = ∅ :=
            Finset.inter_singleton_of_notMem heS
          simp [hp1, hp2, vbarSum]
        rw [hzero]
        exact hμ
    · -- the good is sold
      subst hEa; subst hFa
      have hrw : vbarSum w p (∅ : Finset G) + (∑ g ∈ ({e} : Finset G), (vbar w p g - p g)) + c
          = vbar w p e - p e + c := by simp [vbarSum]
      rw [hrw] at haux
      by_cases hmem : ∃ j, e ∈ E.part j
      · obtain ⟨j, hj⟩ := hmem
        have := vbar_le_of_mem_part E hp hj
        linarith
      · push_neg at hmem
        have hzero : eventCost E ∅ {e} c = c - p e := by
          simp only [eventCost, Finset.empty_union, Finset.sum_singleton]
          have hp1 : ∀ j, E.part j ∩ ({e} : Finset G) = ∅ :=
            fun j => Finset.inter_singleton_of_notMem (hmem j)
          have hp2 : E.sell ∩ ({e} : Finset G) = ∅ :=
            Finset.inter_singleton_of_notMem heS
          simp [hp1, hp2, vbarSum]
          ring
        rw [hzero]
        linarith
  · -- `ℓ₂`
    obtain ⟨hval, hF⟩ := h2
    have hFzero : ∑ g ∈ Fa, (vbar w p g - p g) ≤ 0 := by
      refine Finset.sum_nonpos (fun g hg => ?_)
      rcases hF g hg with h | h
      · exact le_of_eq (by simp only [vbar, max_eq_left h, sub_self])
      · exact le_of_eq (hsell_zero g h)
    have : t ≤ μ := by rw [ht]; linarith
    linarith
  · -- `ℓ₃`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, _, hvf, _, hpf⟩, hc0, hbundle⟩ := h3
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    have : vbar w p f - p f ≤ t - (μ - t) := by linarith
    linarith
  · -- `ℓ₄`
    obtain ⟨⟨e, hEa, _, _⟩, ⟨f, hFa, _, hvf, _, hpf⟩, hc0, hbundle⟩ := h4
    subst hFa
    have hFsum : ∑ g ∈ ({f} : Finset G), (vbar w p g - p g) = vbar w p f - p f := by simp
    rw [hFsum] at haux
    have : vbar w p f - p f ≤ t - (μ - t) := by linarith
    linarith
end FairSelling
