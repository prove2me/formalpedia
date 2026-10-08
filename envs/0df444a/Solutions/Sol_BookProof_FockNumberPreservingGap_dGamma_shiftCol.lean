-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.dGamma_shiftCol
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:19:54.130013+00:00
-- url     : https://prove2.me/submissions/580c909e-6fff-49e3-aa11-205d6913377c

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.dGamma_shiftCol
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_shiftCol_apply
import Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_sub
import Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_smul
import Theorems.Thm_BookProof_FockSecondQuantization_dGamma_eq_sum
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (col : ℕ → (ℕ →₀ ℂ)) (mu : ℝ) (u : FockAlg) :
    dGamma (shiftCol col mu) u
      = dGamma col u - ((mu : ℝ) : ℂ) • dGamma numberCol u := by

  classical
  have hmod : modes u ⊆ modes u := subset_rfl
  have hterm : ∀ k : ℕ, creVec (shiftCol col mu k) (annA k u)
      = creVec (col k) (annA k u) - ((mu : ℝ) : ℂ) • creVec (numberCol k) (annA k u) := by
    intro k
    rw [shiftCol_apply, creVec_sub, creVec_smul]
  rw [dGamma_eq_sum (shiftCol col mu) hmod, dGamma_eq_sum col hmod,
    dGamma_eq_sum numberCol hmod, Finset.smul_sum]
  simp only [hterm]
  rw [Finset.sum_sub_distrib]
