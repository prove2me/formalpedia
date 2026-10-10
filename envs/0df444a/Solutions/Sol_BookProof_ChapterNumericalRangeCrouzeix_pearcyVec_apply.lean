-- Prove2me | solution 1 for BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T08:20:38.929978+00:00
-- url     : https://prove2.me/submissions/cb771d3c-dea5-4ec2-af5b-f908b426e70d

-- Generated from ChapterNumericalRangeCrouzeix.lean — solution of BookProof.ChapterNumericalRangeCrouzeix.pearcyVec_apply
import Mathlib
import Definitions.Def_ChapterNumericalRangeCrouzeix
open BookProof.ChapterNumericalRangeCrouzeix



open scoped InnerProductSpace


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution (A : E →L[ℂ] E) (c : ℂ) (n : ℕ) (y : E) :
    pearcyVec A c n y - c • A (pearcyVec A c n y) = y - c ^ n • (A ^ n) y := by

  set v : ℕ → E := fun m => c ^ m • (A ^ m) y with hv
  have hcomm : ∀ (m : ℕ), A ((A ^ m) y) = (A ^ m) (A y) := by
    intro m
    rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← pow_succ',
      ← pow_succ]
  have hpow : ∀ (m : ℕ) (z : E), (A ^ m) z = (⇑A)^[m] z := by
    intro m z
    induction m generalizing z with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ContinuousLinearMap.mul_apply, Function.iterate_succ_apply, ih]
  have hcommI : ∀ (m : ℕ), A ((⇑A)^[m] y) = (⇑A)^[m] (A y) := fun m => by
    rw [← hpow m y, ← hpow m (A y)]
    exact hcomm m
  have hstep : ∀ m, c • A (v m) = v (m + 1) := by
    intro m
    simp [hv, map_smul, pow_succ, pow_succ', smul_smul, mul_comm, hcommI]
  have h1 : A (pearcyVec A c n y) = ∑ m ∈ Finset.range n, A (v m) := by
    simp [pearcyVec, hv, map_sum]
  calc pearcyVec A c n y - c • A (pearcyVec A c n y)
      = (∑ m ∈ Finset.range n, v m) - ∑ m ∈ Finset.range n, c • A (v m) := by
        rw [h1, Finset.smul_sum]; rfl
    _ = ∑ m ∈ Finset.range n, (v m - v (m + 1)) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun m _ => by rw [hstep m]
    _ = v 0 - v n := Finset.sum_range_sub' v n
    _ = y - c ^ n • (A ^ n) y := by simp [hv]
