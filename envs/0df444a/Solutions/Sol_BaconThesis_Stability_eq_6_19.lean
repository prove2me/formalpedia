-- Prove2me | solution 1 for BaconThesis.Stability.eq_6_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:17:43.6098+00:00
-- url     : https://prove2.me/submissions/c59f510c-60b8-4a00-b9f2-cd711918aec0

import Mathlib
import Definitions.Def_BaconThesis_Stability_blockOp
import Definitions.Def_BaconThesis_Stability_upsilon

namespace Aux_BaconEq619
open BaconThesis.Stability

lemma left {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ) (J : 𝒥)
    (X : ∀ K, Matrix (Fin (d K)) (Fin (d K)) ℂ)
    (Y : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (i j : Fin (n J)) (k k₂ : Fin (d J)) :
    (blockOp n d X * Y) ⟨J, (i, k)⟩ ⟨J, (j, k₂)⟩
      = ∑ k' : Fin (d J), X J k k' * Y ⟨J, (i, k')⟩ ⟨J, (j, k₂)⟩ := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · simp [blockOp, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
  · intro K _ hK
    apply Finset.sum_eq_zero
    intro y _
    rw [blockOp, Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hK), zero_mul]
  · intro h; exact absurd (Finset.mem_univ J) h

lemma right {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ) (J : 𝒥)
    (X : ∀ K, Matrix (Fin (d K)) (Fin (d K)) ℂ)
    (Y : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ)
    (i j : Fin (n J)) (k k₂ : Fin (d J)) :
    (Y * blockOp n d X) ⟨J, (i, k)⟩ ⟨J, (j, k₂)⟩
      = ∑ k' : Fin (d J), Y ⟨J, (i, k)⟩ ⟨J, (j, k')⟩ * X J k' k₂ := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single J]
  · simp [blockOp, Matrix.blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Fintype.sum_prod_type]
  · intro K _ hK
    apply Finset.sum_eq_zero
    intro y _
    rw [blockOp, Matrix.blockDiagonal'_apply_ne _ _ _ hK, mul_zero]
  · intro h; exact absurd (Finset.mem_univ J) h

end Aux_BaconEq619

open BaconThesis.Stability in
theorem solution {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ) (J : 𝒥)
    (X : ∀ K, Matrix (Fin (d K)) (Fin (d K)) ℂ)
    (Y : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ) :
    upsilon n d J (blockOp n d X * Y) = upsilon n d J (Y * blockOp n d X) := by
  ext i j
  simp only [upsilon, WildeQIT.partialTraceRight, Matrix.of_apply, Matrix.submatrix_apply]
  rw [Finset.sum_congr rfl (fun k _ => Aux_BaconEq619.left n d J X Y i j k k),
    Finset.sum_congr rfl (fun k _ => Aux_BaconEq619.right n d J X Y i j k k)]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => mul_comm _ _))
