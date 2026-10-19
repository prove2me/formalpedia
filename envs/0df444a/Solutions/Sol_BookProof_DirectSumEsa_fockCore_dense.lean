-- Prove2me | solution 1 for BookProof.DirectSumEsa.fockCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:51:38.421768+00:00
-- url     : https://prove2.me/submissions/f2fb839a-b1e8-4776-8c0e-b45a5df25178

import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_boundedEnergyCore_dense
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockCore_dense
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


theorem solution {w : ℝ → ℝ} (hw : Measurable w) :
    Dense ((fockCore w : Submodule ℂ fockSpace) : Set fockSpace) := by
  apply BookProof.DirectSumEsa.dsCore_dense
  intro n
  exact BookProof.NavierStokesFlow.FockContinuum.boundedEnergyCore_dense _
    (Finset.univ.measurable_sum fun k _ => hw.comp (measurable_pi_apply k))

