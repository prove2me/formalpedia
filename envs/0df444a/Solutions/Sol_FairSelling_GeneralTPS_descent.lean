-- Prove2me | solution 1 for FairSelling.GeneralTPS.descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:16.466736+00:00
-- url     : https://prove2.me/submissions/71b2389d-84bd-45af-998c-66860806ffbb

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_GeneralTPS_total_nonneg
import Theorems.Thm_FairSelling_GeneralTPS_descent_inner
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.GeneralTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.GeneralTPS
theorem _root_.solution (hp : ∀ g, 0 ≤ p g) (heps : 0 < eps)
    (hstep : ImprovementStep v p eps) :
    ∀ (c : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
  intro c
  induction c with
  | zero =>
    intro s hs hc
    refine ⟨s, hs, ?_⟩
    have h1 : s.served.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ s.served)
    have : s.served.card = n := by omega
    exact Finset.eq_univ_of_card _ (by simpa using this)
  | succ c ihc =>
    intro s hs hc
    -- a number of steps that certainly exhausts the utility budget
    obtain ⟨b, hbb⟩ : ∃ b : ℕ, totalBound v p ≤ (b : ℝ) * eps := by
      obtain ⟨b, hb⟩ := exists_nat_gt (totalBound v p / eps)
      exact ⟨b, by rw [div_lt_iff₀ heps] at hb; linarith⟩
    refine descent_inner v p eps hp heps hstep c ihc b s hs hc ?_
    have := total_nonneg v p eps hp hs
    linarith
end FairSelling.GeneralTPS
