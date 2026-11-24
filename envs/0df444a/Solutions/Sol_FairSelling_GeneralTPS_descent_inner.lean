-- Prove2me | solution 1 for FairSelling.GeneralTPS.descent_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:25.667832+00:00
-- url     : https://prove2.me/submissions/fbfe4d19-2ed6-4d59-ab01-9c7572f61803

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefx
import Definitions.Def_RequestProject_TPSSefxGeneral
import Theorems.Thm_FairSelling_GeneralTPS_total_le_bound
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
    (hstep : ImprovementStep v p eps) (c : ℕ)
    (IH : ∀ s : Stage G n, s.Good v p eps → n - s.served.card ≤ c →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ) :
    ∀ (b : ℕ) (s : Stage G n), s.Good v p eps → n - s.served.card ≤ c + 1 →
      totalBound v p - (b : ℝ) * eps ≤ s.total v p →
      ∃ s' : Stage G n, s'.Good v p eps ∧ s'.served = Finset.univ := by
  intro b
  induction b with
  | zero =>
    intro s hs _ hb
    by_cases hfull : s.served = Finset.univ
    · exact ⟨s, hs, hfull⟩
    obtain ⟨s', hs', hprog⟩ := hstep s hs hfull
    rcases hprog with hcard | ⟨_, hval⟩
    · refine IH s' hs' ?_
      have h1 : s'.served.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ s'.served)
      omega
    · exfalso
      have h1 := total_le_bound v p eps hp hs'
      simp only [Nat.cast_zero, zero_mul, sub_zero] at hb
      linarith
  | succ b ihb =>
    intro s hs hc hb
    by_cases hfull : s.served = Finset.univ
    · exact ⟨s, hs, hfull⟩
    obtain ⟨s', hs', hprog⟩ := hstep s hs hfull
    rcases hprog with hcard | ⟨hcard, hval⟩
    · refine IH s' hs' ?_
      have h1 : s'.served.card ≤ n := by
        simpa using Finset.card_le_card (Finset.subset_univ s'.served)
      omega
    · refine ihb s' hs' (by omega) ?_
      push_cast at hb ⊢
      linarith
end FairSelling.GeneralTPS
