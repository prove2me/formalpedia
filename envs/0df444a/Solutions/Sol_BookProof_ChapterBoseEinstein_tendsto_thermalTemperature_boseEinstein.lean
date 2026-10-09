-- Prove2me | solution 1 for BookProof.ChapterBoseEinstein.tendsto_thermalTemperature_boseEinstein
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:33:18.513977+00:00
-- url     : https://prove2.me/submissions/b8619309-5acd-43f2-80ee-edbeee8739c7

-- Generated from ChapterBoseEinstein.lean — solution of BookProof.ChapterBoseEinstein.tendsto_thermalTemperature_boseEinstein
import Mathlib
import Definitions.Def_ChapterBoseEinstein
open BookProof.ChapterBoseEinstein



noncomputable section

open Filter Topology


open BookProof.ChapterCoherentTemperature BookProof.ChapterCoherentOccupation

variable {x : ℝ}

variable {x : ℝ}

set_option maxHeartbeats 1000000 in
theorem solution :
    Tendsto (fun x : ℝ => thermalTemperature (boseEinstein x)) atTop (𝓝 (1 / 2)) := by

  have h1 : Tendsto (fun x : ℝ => Real.exp x - 1) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_add tendsto_const_nhds
  have h2 : Tendsto (fun x : ℝ => boseEinstein x) atTop (𝓝 0) := by
    simpa [boseEinstein, one_div] using! h1.inv_tendsto_atTop
  simpa [thermalTemperature] using h2.add (tendsto_const_nhds (x := (1 / 2 : ℝ)))
