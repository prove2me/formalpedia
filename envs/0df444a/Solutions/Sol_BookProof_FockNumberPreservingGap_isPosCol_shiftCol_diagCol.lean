-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:29:12.21716+00:00
-- url     : https://prove2.me/submissions/d3668ba7-a8b5-4bce-858e-077900ddfa38

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.isPosCol_shiftCol_diagCol
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_diagCol
import Theorems.Thm_BookProof_FockOneParticleGap_conj_mul_re
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution {e : ℕ → ℝ} {mu : ℝ} (he : ∀ k, mu ≤ e k) :
    IsPosCol (shiftCol (diagCol e) mu) := by

  classical
  intro S c
  rw [shiftCol_diagCol]
  have hcol : ∀ j k : ℕ, (diagCol (fun k => e k - mu) k) j
      = if j = k then (((e k - mu : ℝ)) : ℂ) else 0 := by
    intro j k
    rw [diagCol, Finsupp.single_apply]
    by_cases h : j = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun hkj : k = j => h hkj.symm)]
  have hsum : (∑ j ∈ S, ∑ k ∈ S,
      (starRingEnd ℂ) (c j) * (diagCol (fun k => e k - mu) k) j * c k)
      = ∑ j ∈ S, (((e j - mu : ℝ)) : ℂ) * ((starRingEnd ℂ) (c j) * c j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_eq_single j]
    · rw [hcol j j, if_pos rfl]; ring
    · intro k _ hkj
      rw [hcol j k, if_neg (fun h : j = k => hkj (h ▸ rfl))]
      ring
    · intro hj'; exact absurd hj hj'
  rw [hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun j _ => ?_
  rw [Complex.re_ofReal_mul, conj_mul_re]
  exact mul_nonneg (by linarith [he j]) (sq_nonneg _)
