-- Prove2me | solution 1 for BookProof.SpectralGapStability.gapAt_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:21.714297+00:00
-- url     : https://prove2.me/submissions/11e23db6-732b-4f05-bcc2-9f78911f4555

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.gapAt_of_tendsto
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
import Theorems.Thm_BookProof_SpectralGapStability_gapAt_perturb
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : ℕ → F →L[ℂ] F} {B : F →L[ℂ] F} {lam d : ℝ}
    (hA : ∀ m, GapAt (A m) lam d)
    (hconv : Tendsto (fun m => ‖A m - B‖) atTop (𝓝 0)) : GapAt B lam d := by

  intro x
  refine le_of_forall_pos_le_add ?_
  intro eps heps
  have hpos : 0 < eps / (‖x‖ + 1) := by positivity
  have hev : ∀ᶠ m in atTop, ‖A m - B‖ < eps / (‖x‖ + 1) :=
    hconv.eventually (gt_mem_nhds hpos)
  obtain ⟨m, hm⟩ := hev.exists
  have hgap := gapAt_perturb (A := A m) (B := B) (lam := lam) (d := d)
    (eps := eps / (‖x‖ + 1)) (hA m) hm.le x
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hsmall : eps / (‖x‖ + 1) * ‖x‖ ≤ eps := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have : (d - eps / (‖x‖ + 1)) * ‖x‖ = d * ‖x‖ - eps / (‖x‖ + 1) * ‖x‖ := by ring
  rw [this] at hgap
  linarith
