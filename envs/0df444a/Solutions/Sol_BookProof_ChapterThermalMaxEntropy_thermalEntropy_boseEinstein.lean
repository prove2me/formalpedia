-- Prove2me | solution 1 for BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:11:22.397869+00:00
-- url     : https://prove2.me/submissions/e5b51163-abea-4cb6-8979-23759fafe86e

-- Generated from ChapterThermalMaxEntropy.lean — solution of BookProof.ChapterThermalMaxEntropy.thermalEntropy_boseEinstein
import Mathlib
import Definitions.Def_ChapterThermalMaxEntropy
import Theorems.Thm_BookProof_ChapterThermalMaxEntropy_thermalEntropy_eq
import Theorems.Thm_BookProof_ChapterBoseEinstein_boseEinstein_pos
import Theorems.Thm_BookProof_ChapterBoseEinstein_exp_sub_one_pos
import Theorems.Thm_BookProof_ChapterBoseEinstein_thermalRatio_boseEinstein
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
theorem solution {x : ℝ} (hx : 0 < x) :
    thermalEntropy (boseEinstein x)
      = -Real.log (1 - Real.exp (-x)) + x * boseEinstein x := by

  have hpos := boseEinstein_pos hx
  have hexp := exp_sub_one_pos hx
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos _
  have hone : boseEinstein x + 1 = (1 - Real.exp (-x))⁻¹ := by
    rw [boseEinstein, Real.exp_neg]
    field_simp
    ring
  have hlt : (0 : ℝ) < 1 - Real.exp (-x) := by
    have : Real.exp (-x) < 1 := by
      rw [Real.exp_neg, inv_lt_one_iff₀]
      right; exact Real.one_lt_exp_iff.mpr hx
    linarith
  rw [thermalEntropy_eq hpos, thermalRatio_boseEinstein hx, Real.log_exp, hone, Real.log_inv]
  ring
