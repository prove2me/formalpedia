-- Prove2me | solution 1 for BoydADMM.Constrained.consensus_projection
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:13:53.081339+00:00
-- url     : https://prove2.me/submissions/e7b55ccf-9f89-4807-b514-ffbac46a8ec4

import Definitions.Def_BoydADMM_Constrained_Geometry

open BoydADMM.Constrained
open scoped BigOperators

private lemma sum_centered_local {N n : ℕ} (hN : 0 < N) (v : Blocks N n) :
    ∑ i : Fin N, (v i - avg v) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  simp [avg, smul_smul, Nat.ne_of_gt hN]

private lemma variance_local {N n : ℕ} (hN : 0 < N) (v : Blocks N n) (z : Vec n) :
    blockSqDist v (fun _ => z) =
      blockSqDist v (fun _ => avg v) + (N : ℝ) * ‖avg v - z‖ ^ 2 := by
  have hsplit (i : Fin N) : v i - z = (v i - avg v) + (avg v - z) := by abel
  simp only [blockSqDist]
  simp_rw [hsplit, norm_add_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← sum_inner, sum_centered_local hN v]
  simp [nsmul_eq_mul]

theorem solution {N n : ℕ} (hN : 0 < N) (v : Blocks N n) :
    IsBlockProjection (consensusSet N n) v (fun _ => avg v) := by
  refine ⟨⟨avg v, fun _ => rfl⟩, ?_⟩
  rintro w ⟨z, hz⟩
  have hw : w = fun _ => z := funext hz
  rw [hw, variance_local hN v z]
  exact le_add_of_nonneg_right (by positivity)

#print axioms solution
