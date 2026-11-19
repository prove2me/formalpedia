-- Prove2me | solution 1 for Erdos195.even_halves_0145_0154_not_tree_safe
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T11:55:26.15648+00:00
-- url     : https://prove2.me/submissions/7a679988-d6fa-43e8-b073-f4c2a092ddcf

import Definitions.Def_Erdos195_tree
import Theorems.Thm_Erdos195_exists_treeLt_safe_iff
import Mathlib.Data.List.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Erdos195

private lemma pv2_of_odd {n : ℤ} (h : n % 2 = 1) : padicValInt 2 n = 0 := by
  have : ¬ (2 : ℤ) ∣ n := by
    intro hd
    have : n % 2 = 0 := Int.emod_eq_zero_of_dvd hd
    omega
  exact padicValInt.eq_zero_of_not_dvd this

private lemma pv2_one : padicValInt 2 (1 : ℤ) = 0 := pv2_of_odd (by decide)

private lemma pv2_three : padicValInt 2 (3 : ℤ) = 0 := pv2_of_odd (by decide)

/-- If `(0,1)` and `(1,4)` are both open in-order pairs, they occupy the root node
and force opposite bits, so the word is not tree-safe. -/
private lemma not_safe_of_root_conflict (Q : List ℤ)
    (h0 : (0 : ℤ) ∈ Q) (h1 : (1 : ℤ) ∈ Q) (h4 : (4 : ℤ) ∈ Q)
    (h01 : Q.idxOf 0 < Q.idxOf 1) (h14 : Q.idxOf 1 < Q.idxOf 4)
    (h2 : (2 : ℤ) ∉ Q) (h3 : (3 : ℤ) ∉ Q) (h7 : (7 : ℤ) ∉ Q) (h10 : (10 : ℤ) ∉ Q) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q := by
  intro hS
  rw [exists_treeLt_safe_iff] at hS
  obtain ⟨_, hconf⟩ := hS
  have h01open2 : 2 * (1 : ℤ) - 0 ∉ Q := by
    simpa using h2
  have h01open3 : 3 * (1 : ℤ) - 2 * (0 : ℤ) ∉ Q := by
    simpa using h3
  have h14open2 : 2 * (4 : ℤ) - 1 ∉ Q := by
    simpa using h7
  have h14open3 : 3 * (4 : ℤ) - 2 * (1 : ℤ) ∉ Q := by
    simpa using h10
  have hv : padicValInt 2 ((1 : ℤ) - 0) = padicValInt 2 ((4 : ℤ) - 1) := by
    simp [pv2_one, pv2_three]
  have hr : (0 : ℤ) % 2 ^ padicValInt 2 ((1 : ℤ) - 0) =
      (1 : ℤ) % 2 ^ padicValInt 2 ((1 : ℤ) - 0) := by
    simp [pv2_one]
  have hbits := hconf 0 1 1 4 h0 h1 h01 h01open2 h01open3 h1 h4 h14 h14open2 h14open3 hv hr
  simp [bitOne, pv2_one] at hbits

theorem even_halves_0145_0154_not_tree_safe :
    (¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 4, 5]) ∧
    (¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 5, 4]) := by
  constructor
  · apply not_safe_of_root_conflict <;> decide
  · apply not_safe_of_root_conflict <;> decide

end Erdos195

theorem solution :
    (¬ ∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) [0, 1, 4, 5]) ∧
    (¬ ∃ θ : ℕ → ℤ → Bool, Erdos195.Safe (Erdos195.treeLt θ) [0, 1, 5, 4]) :=
  Erdos195.even_halves_0145_0154_not_tree_safe
