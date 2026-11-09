-- Prove2me | solution 1 for BookProof.L2TensorPower.embPow_succ_tmul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:41:12.500859+00:00
-- url     : https://prove2.me/submissions/8329d470-af7d-4af2-89df-8b393261a541

-- Generated from ChapterL2TensorPowerUnitary.lean — solution of BookProof.L2TensorPower.embPow_succ_tmul
import Mathlib
import Definitions.Def_ChapterL2TensorPowerUnitary
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.L2TensorPower




open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct

noncomputable section


variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]
variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (a : Lp ℂ 2 μ) (t : ((L2Space μ).pow n).carrier) :
    embPow μ (n + 1) (a ⊗ₜ[ℂ] t) = splitIso μ n (prodMk a (embPow μ n t)) := rfl
