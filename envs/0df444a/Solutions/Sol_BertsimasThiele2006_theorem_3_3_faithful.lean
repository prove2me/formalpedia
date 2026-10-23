-- Prove2me | solution 1 for BertsimasThiele2006.theorem_3_3_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:58:05.805428+00:00
-- url     : https://prove2.me/submissions/f63208c4-eadc-4bb3-a82e-4f78fa937879

import Mathlib
import Definitions.Def_RobustInventory_SingleStation_Deviation
import Definitions.Def_RobustInventory_SingleStation_Robust
import Theorems.Thm_RobustInventory_SingleStation_theorem_3_2

open Finset RobustInventory.SingleStation

theorem solution (M : Model)
    (hdem : ∀ k, M.what k ≤ M.wbar k) (d : ℝ) (u : ℕ → ℝ) :
    (∃ (y q : ℕ → ℝ) (r : ℕ → ℕ → ℝ),
      (M.RobustFeasible u y q r ∧ ∀ k < M.T, u k ≤ d) ∧
      ∀ (u' y' q' : ℕ → ℝ) (r' : ℕ → ℕ → ℝ),
        (M.RobustFeasible u' y' q' r' ∧ ∀ k < M.T, u' k ≤ d) →
          M.robustObjective u y ≤ M.robustObjective u' y') ↔
    ((∀ k < M.T, 0 ≤ u k ∧ u k ≤ d) ∧
      ∀ u' : ℕ → ℝ, (∀ k < M.T, 0 ≤ u' k ∧ u' k ≤ d) →
        M.nominalCost M.wmod u ≤ M.nominalCost M.wmod u') := by
  obtain ⟨hd, -, -, -⟩ := theorem_3_2 M
  constructor
  · rintro ⟨y, q, r, ⟨hfeas, hcap⟩, hopt⟩
    have hu0 : ∀ k < M.T, 0 ≤ u k := fun k hk => (hfeas k hk).1
    refine ⟨fun k hk => ⟨hu0 k hk, hcap k hk⟩, ?_⟩
    intro u' hu'
    obtain ⟨y', q', r', hf', heq'⟩ := (hd u' (fun k hk => (hu' k hk).1)).2
    have h1 := hopt u' y' q' r' ⟨hf', fun k hk => (hu' k hk).2⟩
    have h2 := (hd u hu0).1 y q r hfeas
    linarith
  · rintro ⟨hu, hmin⟩
    obtain ⟨y, q, r, hf, heq⟩ := (hd u (fun k hk => (hu k hk).1)).2
    refine ⟨y, q, r, ⟨hf, fun k hk => (hu k hk).2⟩, ?_⟩
    rintro u' y' q' r' ⟨hf', hcap'⟩
    have hu'0 : ∀ k < M.T, 0 ≤ u' k := fun k hk => (hf' k hk).1
    have h1 := (hd u' hu'0).1 y' q' r' hf'
    have h2 := hmin u' (fun k hk => ⟨hu'0 k hk, hcap' k hk⟩)
    linarith
