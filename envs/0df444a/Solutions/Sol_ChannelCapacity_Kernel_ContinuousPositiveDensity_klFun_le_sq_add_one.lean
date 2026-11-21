-- Prove2me | solution 1 for ChannelCapacity.Kernel.ContinuousPositiveDensity.klFun_le_sq_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:42:30.712385+00:00
-- url     : https://prove2.me/submissions/f5d67d66-e8d9-428a-b1e2-1666e46a0b5e

module
public import Definitions.Def_LeanPool_ChannelCapacity_Capacity
public import Definitions.Def_LeanPool_ChannelCapacity_ChainRule
public import Definitions.Def_LeanPool_ChannelCapacity_KernelCompositionKullbackLeibler
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Definitions.Def_LeanPool_ChannelCapacity_Discharged

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
open ChannelCapacity
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable [TopologicalSpace α] [TopologicalSpace β]
open ChannelCapacity.Kernel
open ChannelCapacity.Kernel.ContinuousPositiveDensity
variable {k : Kernel α β} [IsMarkovKernel k] [OpensMeasurableSpace α] {ν : Measure β}
namespace ChannelCapacity.Kernel.ContinuousPositiveDensity
theorem _root_.solution {x B : ℝ} (hx : 0 ≤ x) (hB : x ≤ B) :
    InformationTheory.klFun x ≤ B ^ 2 + 1 := by
  have hlog : Real.log x ≤ x := Real.log_le_self hx
  calc
    InformationTheory.klFun x = x * Real.log x + 1 - x := rfl
    _ ≤ x * x + 1 - x := by
      gcongr
    _ ≤ B ^ 2 + 1 := by
      nlinarith
end ChannelCapacity.Kernel.ContinuousPositiveDensity
