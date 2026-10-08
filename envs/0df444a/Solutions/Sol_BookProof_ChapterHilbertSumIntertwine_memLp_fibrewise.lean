-- Prove2me | solution 1 for BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T09:05:10.476386+00:00
-- url     : https://prove2.me/submissions/cc130fb0-6d97-4fb7-ad62-b8b108eaaa41

-- Generated from ChapterHilbertSumIntertwine.lean — solution of BookProof.ChapterHilbertSumIntertwine.memLp_fibrewise
import Mathlib
import Definitions.Def_ChapterHilbertSumIntertwine
open BookProof.ChapterHilbertSumIntertwine



open scoped InnerProductSpace



variable {ι : Type*}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*}
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]

set_option maxHeartbeats 1000000 in
theorem solution (B : ∀ i, G i →L[ℂ] G i) (hB : ∀ i u, ‖B i u‖ ≤ ‖u‖)
    (w : lp G 2) : Memℓp (fun i => B i (w i)) 2 := by

  have htr : ((2 : ENNReal)).toReal = (2 : ℝ) := by norm_num
  have hw : Summable fun i => ‖w i‖ ^ (2 : ℝ) := by
    have h := (memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num)).1 (lp.memℓp w)
    simpa only [htr] using h
  refine memℓp_gen ?_
  simp only [htr]
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _)
    (fun i => ?_) hw
  exact Real.rpow_le_rpow (norm_nonneg _) (hB i (w i)) (by norm_num)
