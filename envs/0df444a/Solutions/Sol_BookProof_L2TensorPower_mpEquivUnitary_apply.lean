-- Prove2me | solution 1 for BookProof.L2TensorPower.mpEquivUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:41:20.200584+00:00
-- url     : https://prove2.me/submissions/19fbe0a9-4552-41f3-a073-7bdff4556f80

-- Generated from ChapterL2TensorPowerUnitary.lean — solution of BookProof.L2TensorPower.mpEquivUnitary_apply
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
theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μa : Measure α} {μb : Measure β} (f : α → β) (g : β → α) (hf : MeasurePreserving f μa μb)
    (hg : MeasurePreserving g μb μa) (hgf : ∀ x, g (f x) = x) (h : Lp ℂ 2 μb) :
    (mpEquivUnitary f g hf hg hgf h : α → ℂ) =ᵐ[μa] fun x => (h : β → ℂ) (f x) := Lp.coeFn_compMeasurePreserving h hf
