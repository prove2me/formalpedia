-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_gap_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:05.644988+00:00
-- url     : https://prove2.me/submissions/e0540dfd-bd19-4647-b969-4be1ef0b471a

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_gap_quadForm
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_le_confEnergy
import Theorems.Thm_BookProof_FockOneParticleGap_norm_toLp_sq
import Theorems.Thm_BookProof_FockOneParticleGap_re_inner_dGamma_diagCol
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k)
    {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by

  rw [re_inner_dGamma_diagCol, norm_toLp_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hα) h0
  exact mul_le_mul_of_nonneg_right (le_confEnergy hmu he hα0) (sq_nonneg ‖u α‖)
