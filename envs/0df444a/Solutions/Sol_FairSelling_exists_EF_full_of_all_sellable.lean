-- Prove2me | solution 1 for FairSelling.exists_EF_full_of_all_sellable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:48:58.23025+00:00
-- url     : https://prove2.me/submissions/2ea74e52-f81e-4eb3-bf45-91f0190a6578

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaTen

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (hn : 0 < n) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧ EF v p o ∧ SEFX v p o := by
  classical
  refine ⟨⟨Finset.univ, fun _ => ∅, fun _ => (∑ g, p g) / n⟩, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j; simp
  · intro j k _; simp
  · intro j
    have : 0 ≤ ∑ g, p g := Finset.sum_nonneg fun g _ => hp g
    positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  · exact Finset.Subset.refl _
  · simp [Outcome.AllocatesAll]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)]
  · intro i j; simp
  · intro i j
    exact ⟨fun _ => by simp, fun _ => Or.inr fun g hg => absurd hg (by simp)⟩
end FairSelling
