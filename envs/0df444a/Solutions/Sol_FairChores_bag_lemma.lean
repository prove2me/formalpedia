-- Prove2me | solution 1 for FairChores.bag_lemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:25:58.158664+00:00
-- url     : https://prove2.me/submissions/83edfbe5-99fb-4f09-9794-61f5b627eff7

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
import Theorems.Thm_FairChores_bag_aux
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
variable {c p mu}
omit [Fintype T]
namespace FairChores
theorem _root_.solution (hc : ∀ i t, 0 ≤ c i t) (hp : ∀ t, 0 ≤ p t) (hmu : ∀ i, 0 < mu i)
    {A : Finset (Fin n)} (hA : A.Nonempty) (R : Finset T) :
    BagGoal c p mu A R := by
  classical
  obtain ⟨j0, hj0⟩ := hA
  refine bag_aux hc hp hmu A R (R \ (∅ ∪ ∅)).card ∅ ∅ (by simp) (by simp) (by simp) le_rfl
    (fun j _ => Or.inr (by simp)) (fun _ t ht => absurd ht (by simp))
    ⟨j0, hj0, by simpa [cbarSum] using hmu j0⟩
end FairChores
