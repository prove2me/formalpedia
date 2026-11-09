-- Prove2me | solution 1 for BookProof.L2TensorPower.l2dSpace_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:41:23.904217+00:00
-- url     : https://prove2.me/submissions/81751f95-8bd9-4fc2-960c-b65eff0deeb1

-- Generated from ChapterL2TensorPowerUnitary.lean — solution of BookProof.L2TensorPower.l2dSpace_eq
import Mathlib
import Definitions.Def_ChapterL2TensorPowerUnitary
import Definitions.Def_ChapterNsScalarVectorCurry
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterTensorGraphCore
open BookProof.L2TensorPower




open MeasureTheory BookProof.TensorCore BookProof.NsScalarVectorCurry
open BookProof.SecondQuantizationCore
open scoped TensorProduct
open BookProof.HermiteProductCore
open BookProof.TensorCore

noncomputable section


variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]

variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
  {μ : Measure V} {ν : Measure W} [SigmaFinite μ] [SigmaFinite ν]
variable {V : Type} [MeasurableSpace V] (μ : Measure V) [SigmaFinite μ]

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) :
    BookProof.YangMillsNonAbelianEsa.L2dSpace d = L2Space (volume : Measure (Vd d)) := rfl
