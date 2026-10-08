-- Prove2me | solution 1 for BregmanRelax.Remotest.lemma1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:42:00.957986+00:00
-- url     : https://prove2.me/submissions/803fb172-bdeb-461d-a16a-5699f59f9d31

import Mathlib
import Definitions.Def_BregmanRelax_Remotest_DConditions

set_option autoImplicit false

open BregmanRelax.Remotest in
theorem solution {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    {ι : Type*} {A : ι → Set X} {S : Set X} {D : X → X → ℝ} {P : ι → X → X}
    (hA : BregmanRelax.Cyclic.DConditions A S D P) (i : ι) (z : X) (hz : z ∈ A i ∩ S) (y : X) (hy : y ∈ S) :
    D (P i y) y ≤ D z y - D z (P i y) := by
  obtain ⟨hPA, hmin⟩ := hA.proj i y hy
  have hconv := hA.convexOn i y hy
  have hPP : D (P i y) (P i y) = 0 := (hA.eq_zero_iff _ hPA.2 _ hPA.2).2 rfl
  have hlim := hA.deriv_zero (P i y) hPA.2 z hz.2
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
      D (P i y) y - D (P i y + t • (z - P i y)) (P i y) / t ≤ D z y - D z (P i y) := by
    intro t ht0 ht1
    have hw : P i y + t • (z - P i y) = (1 - t) • P i y + t • z := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hmem : (1 - t) • P i y + t • z ∈ A i ∩ S :=
      hconv.1 hPA hz (by linarith) ht0.le (by ring)
    have h1 := hconv.2 hPA hz (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (by ring)
    have h2 := hmin _ hmem
    simp only [smul_eq_mul] at h1
    rw [hPP, ← hw] at h1
    rw [← hw] at h2
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ ht0]
    nlinarith
  have htend : Filter.Tendsto
      (fun t : ℝ => D (P i y) y - D (P i y + t • (z - P i y)) (P i y) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (D (P i y) y - 0)) :=
    tendsto_const_nhds.sub hlim
  rw [sub_zero] at htend
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
  exact key t ht.1 ht.2.le
