-- Prove2me | solution 1 for BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:25.078275+00:00
-- url     : https://prove2.me/submissions/3d7066d2-0089-4af6-90a0-7184798f94b2

-- Generated from ChapterThermalMaxEntropy.lean — solution of BookProof.ChapterThermalMaxEntropy.shannonEntropy_le_thermalEntropy
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Theorems.Thm_BookProof_ChapterThermalMaxEntropy_log_thermalProb
import Theorems.Thm_BookProof_ChapterThermalMaxEntropy_thermalEntropy_eq
import Theorems.Thm_BookProof_ChapterThermalMaxEntropy_gibbs_pointwise
import Theorems.Thm_BookProof_ChapterCoherentOccupation_thermalProb_summable
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_nonneg
import Theorems.Thm_BookProof_ChapterCoherentTemperature_thermalProb_tsum_one
import Definitions.Def_ChapterCoherentOccupation
import Definitions.Def_ChapterBoseEinstein
import Definitions.Def_ChapterCoherentTemperature
open BookProof.ChapterThermalMaxEntropy



noncomputable section


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation
open BookProof.ChapterBoseEinstein

variable {nbar : ℝ}

variable {nbar : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (h : 0 < nbar) (s : Finset ℕ) (p : ℕ → ℝ)
    (hp : ∀ n ∈ s, 0 ≤ p n) (hsum : ∑ n ∈ s, p n = 1)
    (hmean : ∑ n ∈ s, (n : ℝ) * p n = nbar) :
    -∑ n ∈ s, p n * Real.log (p n) ≤ thermalEntropy nbar := by

  have h0 : (0 : ℝ) ≤ nbar := le_of_lt h
  have sP := thermalProb_summable h0
  have hqsum : ∑ n ∈ s, thermalProb nbar n ≤ 1 := by
    have := sP.sum_le_tsum s (fun n _ => thermalProb_nonneg h0 n)
    rwa [thermalProb_tsum_one h0] at this
  have hstep : ∑ n ∈ s, (p n * Real.log (thermalProb nbar n) - p n * Real.log (p n))
      ≤ ∑ n ∈ s, (thermalProb nbar n - p n) :=
    Finset.sum_le_sum fun n hn => gibbs_pointwise h (hp n hn) n
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum] at hstep
  have hcross : ∑ n ∈ s, p n * Real.log (thermalProb nbar n)
      = -Real.log (nbar + 1) + Real.log (thermalRatio nbar) * nbar := by
    have hterm : ∀ n ∈ s, p n * Real.log (thermalProb nbar n)
        = (-Real.log (nbar + 1)) * p n + Real.log (thermalRatio nbar) * ((n : ℝ) * p n) := by
      intro n _; rw [log_thermalProb h n]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsum, hmean]
    ring
  rw [hcross] at hstep
  rw [thermalEntropy_eq h]
  linarith
