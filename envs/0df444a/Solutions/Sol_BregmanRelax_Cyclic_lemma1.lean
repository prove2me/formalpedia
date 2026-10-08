-- Prove2me | solution 1 for BregmanRelax.Cyclic.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:22:32.827047+00:00
-- url     : https://prove2.me/submissions/0fef4a2c-fdc6-4ee9-9004-3b955bccf427

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions

open BregmanRelax.Cyclic in
theorem solution {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : DConditions A S D P) (i : ι) (z : X) (hz : z ∈ A i ∩ S) (y : X) (hy : y ∈ S) :
    D (P i y) y ≤ D z y - D z (P i y) := by
  obtain ⟨hPmem, hmin⟩ := hA.proj i y hy
  have hconv := hA.convexOn i y hy
  have hPP : D (P i y) (P i y) = 0 := (hA.eq_zero_iff _ hPmem.2 _ hPmem.2).2 rfl
  have hlim := hA.deriv_zero (P i y) hPmem.2 z hz.2
  -- key: for t ∈ (0,1), D(Py,y) - G(z) ≤ D(zt,Py)/t
  have hev : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      D (P i y) y - (D z y - D z (P i y)) ≤ D (P i y + t • (z - P i y)) (P i y) / t := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have heq : (1 - t) • P i y + t • z = P i y + t • (z - P i y) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hmemt : P i y + t • (z - P i y) ∈ A i ∩ S := by
      rw [← heq]
      exact hconv.1 hPmem hz (by linarith) ht0.le (by ring)
    have h1 := hconv.2 hPmem hz (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    rw [heq] at h1
    simp only [smul_eq_mul, hPP, sub_zero] at h1
    have h2 := hmin _ hmemt
    rw [le_div_iff₀ ht0]
    nlinarith
  have := ge_of_tendsto hlim hev
  linarith
