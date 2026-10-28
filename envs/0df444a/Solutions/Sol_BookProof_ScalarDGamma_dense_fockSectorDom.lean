-- Prove2me | solution 1 for BookProof.ScalarDGamma.dense_fockSectorDom
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-25T02:19:24.393277+00:00
-- url     : https://prove2.me/submissions/bda695fd-b8bf-4809-bb80-e09e6d575c6a

-- Generated from ChapterScalarDGammaEsa.lean — solution of BookProof.ScalarDGamma.dense_fockSectorDom
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Theorems.Thm_BookProof_ScalarDGamma_sectorDom_top
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ScalarDGamma




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.GraphCore
open BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

variable (Hs : IPSpace) (c : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    Dense ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) :
      Set (fockSector Hs n)) := by

  have h : ((fockSectorDom Hs ⊤ n : Submodule ℂ (fockSector Hs n)) : Set (fockSector Hs n))
      = Set.range (sectorEmb Hs n) := by
    rw [fockSectorDom, sectorDom_top, pushDom, Submodule.map_top, LinearMap.coe_range]
    rfl
  rw [h]
  exact UniformSpace.Completion.denseRange_coe
