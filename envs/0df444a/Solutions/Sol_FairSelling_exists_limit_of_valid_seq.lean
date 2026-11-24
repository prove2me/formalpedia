-- Prove2me | solution 1 for FairSelling.exists_limit_of_valid_seq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:25.280287+00:00
-- url     : https://prove2.me/submissions/a95af753-a032-444b-a312-428f52b93b42

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Theorems.Thm_FairSelling_money_le_proceeds
import Theorems.Thm_FairSelling_exists_class_subseq

set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution {p : G → ℝ} (o : ℕ → Outcome G n)
    (hval : ∀ k, (o k).Valid p) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (P : Fin n → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) ∧
      Tendsto (fun k => (o (φ k)).money) atTop (𝓝 P) := by
  classical
  obtain ⟨S, A, φ₁, hφ₁, hS, hA⟩ := exists_class_subseq o
  set C : ℝ := max (∑ g ∈ S, p g) 0 with hC
  have hCnonneg : 0 ≤ C := le_max_right _ _
  have hmem : ∀ k, (o (φ₁ k)).money ∈ Metric.closedBall (0 : Fin n → ℝ) C := by
    intro k
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hCnonneg).2 fun j => ?_
    have h0 : 0 ≤ (o (φ₁ k)).money j := (hval (φ₁ k)).2.2.1 j
    have h1 : (o (φ₁ k)).money j ≤ ∑ g ∈ S, p g := by
      have := money_le_proceeds (hval (φ₁ k)) j
      rwa [hS k] at this
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact le_trans h1 (le_max_left _ _)
  obtain ⟨P, -, φ₂, hφ₂, htend⟩ :=
    tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hmem
  refine ⟨S, A, P, φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun k => hS _, fun k => hA _, htend⟩
end FairSelling
