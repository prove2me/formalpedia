-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:27.296168+00:00
-- url     : https://prove2.me/submissions/de19973b-d5fb-482b-8130-18d347466f4f

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_duhamel
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

set_option maxHeartbeats 1000000 in
theorem solution (T S : UnboundedSelfAdjoint H) (chi : T.domain)
    (t : ℝ) {C : ℝ}
    (hC : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      ‖T.resCLM 1 (T.stoneU s (T.shift 1 chi)) - S.resCLM 1 (T.stoneU s (T.shift 1 chi))‖ ≤ C) :
    ‖S.resCLM 1 (T.stoneU t (chi : H)) - S.stoneU t (S.resCLM 1 (chi : H))‖ ≤ C * |t| := by

  set g : ℝ → H := fun r => S.stoneU (t - r) (S.resCLM 1 (T.stoneU r (chi : H))) with hg
  set g' : ℝ → H := fun r => Complex.I • S.stoneU (t - r)
    (T.resCLM 1 (T.stoneU r (T.shift 1 chi)) - S.resCLM 1 (T.stoneU r (T.shift 1 chi))) with hg'
  have hderiv : ∀ r, HasDerivAt g (g' r) r := fun r => hasDerivAt_duhamel T S chi t r
  have hnorm : ∀ r ∈ Set.uIcc (0 : ℝ) t, ‖g' r‖ ≤ C := by
    intro r hr
    have h1 : ‖g' r‖
        = ‖T.resCLM 1 (T.stoneU r (T.shift 1 chi)) - S.resCLM 1 (T.stoneU r (T.shift 1 chi))‖ := by
      rw [hg']
      simp only [norm_smul, Complex.norm_I, one_mul]
      exact S.norm_stoneU_apply _ _
    rw [h1]
    exact hC r hr
  have hconv : Convex ℝ (Set.uIcc (0 : ℝ) t) := convex_uIcc 0 t
  have hmv := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hderiv r).hasDerivWithinAt) hnorm Set.left_mem_uIcc Set.right_mem_uIcc
  have hgt : g t = S.resCLM 1 (T.stoneU t (chi : H)) := by
    rw [hg]
    simp only [sub_self, S.stoneU_zero, ContinuousLinearMap.one_apply]
  have hg0 : g 0 = S.stoneU t (S.resCLM 1 (chi : H)) := by
    rw [hg]
    simp only [sub_zero, T.stoneU_zero, ContinuousLinearMap.one_apply]
  rw [hgt, hg0] at hmv
  simpa using hmv
