-- Prove2me | solution 1 for ExAnteExPost.RPS.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T08:46:25.317785+00:00
-- url     : https://prove2.me/submissions/8c23171a-96d0-4ec4-9dfd-1a1c917768a6

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model
import Theorems.Thm_ExAnteExPost_RPS_eating_stage
import Theorems.Thm_ExAnteExPost_RPS_eating_envy_free
import Theorems.Thm_ExAnteExPost_RPS_implements_rps_succ
import Theorems.Thm_ExAnteExPost_RPS_lemma_2

open Finset ExAnteExPost.RPS

namespace RPSRed

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

lemma util_lin (I : Instance N G) {ι : Type*} (s : Finset ι) (i : N) (a : G → ℝ) (w : ι → ℝ)
    (b : ι → G → ℝ) :
    util I i (fun g => a g + ∑ k ∈ s, w k * b k g) =
      util I i a + ∑ k ∈ s, w k * util I i (b k) := by
  simp only [util, add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Ex-ante envy-freeness of any number of stages, by induction on the number of stages. -/
theorem impl_ef [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D)
    (T : ℕ) : ∀ M' : Finset G, IsEF I (implements (rps pick D T M')) := by
  induction T with
  | zero =>
    intro M' i h
    have : implements (rps pick D 0 M') = fun _ _ => 0 := by
      funext j g; simp [implements, rps, rpsHist, toFrac, unionHist]
    rw [this]
  | succ T ih =>
    intro M' i h
    have hX : ∀ j, implements (rps pick D (T + 1) M') j = fun g => eating pick M' j g +
        ∑ k, (D (eating pick M')).w k *
          implements (rps pick D T (M' \ univ.biUnion ((D (eating pick M')).A k))) j g := by
      intro j; funext g; exact implements_rps_succ I pick hpick D hD T M' j g
    rw [hX h, hX i, util_lin, util_lin]
    have h1 := eating_envy_free I pick hpick M' i h
    have hw : ∀ k, 0 ≤ (D (eating pick M')).w k :=
      fun k => ((hD _ (eating_stage I pick hpick M').1).1 k).1
    have h2 := Finset.sum_le_sum fun k (_ : k ∈ (univ : Finset (Fin (D (eating pick M')).q))) =>
        mul_le_mul_of_nonneg_left
          (ih (M' \ univ.biUnion ((D (eating pick M')).A k)) i h) (hw k)
    linarith

end RPSRed

theorem solution {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]
    [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D) :
    ExAnteEF I (algorithm1 pick D) ∧ ExPostEF1 I (algorithm1 pick D) :=
  ⟨RPSRed.impl_ef I pick hpick D hD (stages N G) univ, lemma_2 I pick hpick D hD⟩
