-- Prove2me | solution 1 for ExplicitExpanders.Delete.spectral_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-20T06:22:03.912894+00:00
-- url     : https://prove2.me/submissions/38aa26e9-5f66-440e-aa8e-60d7de49e614

import Mathlib
import Definitions.Def_ExplicitExpanders_Delete_IsNDLambda
import Definitions.Def_ExplicitExpanders_Delete_Neighbourhoods
import Definitions.Def_ExplicitExpanders_Delete_DeleteAndMatch
import Theorems.Thm_ExplicitExpanders_Delete_eq_9
import Theorems.Thm_ExplicitExpanders_Delete_eq_10
import Theorems.Thm_ExplicitExpanders_Delete_eq_11
import Theorems.Thm_ExplicitExpanders_Delete_construction_regular

set_option autoImplicit false

open ExplicitExpanders.Delete Matrix in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (d : ℕ) (ε : ℝ) (hd : 3 ≤ d) (hε : 0 < ε)
    (hH : IsNDLambda H (Fintype.card V) d (2 * Real.sqrt ((d : ℝ) - 1) + ε / 2))
    (U : Finset V) (hU2 : ∀ z ∈ U, NoCycleOn H (ball H z (⌈2 / ε⌉₊ + 1)))
    (hU3 : ∀ z ∈ U, ∀ z' ∈ U, z ≠ z' → ((2 * ⌈2 / ε⌉₊ + 3 : ℕ) : ℕ∞) ≤ H.edist z z')
    (m : V → V) (hm : IsMatchingOn (nbrSet H U) m) :
    IsNDLambda (deleteAndMatch H U m) (Fintype.card V - U.card) d
      (2 * Real.sqrt ((d : ℝ) - 1) + ε) := by
  obtain rfl : ‹DecidableRel H.Adj› = (fun a b => Classical.propDecidable (H.Adj a b)) :=
    Subsingleton.elim _ _
  classical
  have hr1 : 1 ≤ ⌈2 / ε⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr (by positivity)))
  have hrpos : (0 : ℝ) < (⌈2 / ε⌉₊ : ℝ) := by exact_mod_cast hr1
  have hrε : 1 / (⌈2 / ε⌉₊ : ℝ) ≤ ε / 2 := by
    have h1 : 2 / ε ≤ (⌈2 / ε⌉₊ : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hrpos]
    have h2 : 2 ≤ ε * (⌈2 / ε⌉₊ : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 hε.le
      rwa [mul_div_cancel₀ _ hε.ne'] at this
    linarith
  have hH' := hH
  obtain ⟨hreg, _, _, _, _⟩ := hH'
  obtain ⟨hGreg, hKcard, hA⟩ :=
    ExplicitExpanders.Delete.construction_regular H d ⌈2 / ε⌉₊ hreg hr1 U hU2 hU3 m hm
  refine ⟨hGreg, SimpleGraph.isSymm_adjMatrix _, ?_, ?_, ?_⟩
  · convert hKcard
  · ext v
    rw [show (fun _ : Kept U => (1 : ℝ)) = Function.const _ 1 from rfl,
      SimpleGraph.adjMatrix_mulVec_const_apply, hGreg v]
    simp
  · intro μ f hf0 hsum heig
    by_cases hμ : |μ| ≤ 2 * Real.sqrt ((d : ℝ) - 1)
    · linarith
    rw [not_le] at hμ
    have heig' : (deleteAndMatch H U m).adjMatrix ℝ *ᵥ f = μ • f := by convert heig
    have h11 := ExplicitExpanders.Delete.eq_11 H d ⌈2 / ε⌉₊ hd hreg hr1 U hU2 hU3 m hm f μ heig'
      hμ.le
    have h10 := ExplicitExpanders.Delete.eq_10 H U m hm f
    have h9 := ExplicitExpanders.Delete.eq_9 H (Fintype.card V) d _ hH U f hsum
    have hsplit : f ⬝ᵥ ((deleteAndMatch H U m).adjMatrix ℝ *ᵥ f) =
        f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f) + f ⬝ᵥ ((matchGraph H U m).adjMatrix ℝ *ᵥ f) := by
      rw [hA, Matrix.add_mulVec, dotProduct_add]
    have hS : f ⬝ᵥ ((deleteAndMatch H U m).adjMatrix ℝ *ᵥ f) = μ * ∑ x, f x ^ 2 := by
      rw [heig', dotProduct_smul, smul_eq_mul]
      simp [dotProduct, sq]
    have hpos : 0 < ∑ x, f x ^ 2 := by
      obtain ⟨x, hx⟩ := Function.ne_iff.mp hf0
      exact lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hx : f x ≠ 0))))
        (Finset.single_le_sum (f := fun x => f x ^ 2)
        (fun i _ => sq_nonneg (f i)) (Finset.mem_univ x))
    have habs : |μ| * ∑ x, f x ^ 2 ≤ (2 * Real.sqrt ((d : ℝ) - 1) + ε) * ∑ x, f x ^ 2 := by
      have e1 : |μ| * ∑ x, f x ^ 2 = |f ⬝ᵥ ((deleteAndMatch H U m).adjMatrix ℝ *ᵥ f)| := by
        rw [hS, abs_mul, abs_of_pos hpos]
      rw [e1, hsplit]
      have t := abs_add_le (f ⬝ᵥ ((deleted H U).adjMatrix ℝ *ᵥ f))
        (f ⬝ᵥ ((matchGraph H U m).adjMatrix ℝ *ᵥ f))
      have h3 : 1 / (⌈2 / ε⌉₊ : ℝ) * ∑ x, f x ^ 2 ≤ ε / 2 * ∑ x, f x ^ 2 :=
        mul_le_mul_of_nonneg_right hrε hpos.le
      nlinarith
    exact le_of_mul_le_mul_right habs hpos
