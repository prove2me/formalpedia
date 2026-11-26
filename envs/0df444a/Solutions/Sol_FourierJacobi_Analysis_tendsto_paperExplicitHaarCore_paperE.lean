-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_paperExplicitHaarCore_paperE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:02:08.680601+00:00
-- url     : https://prove2.me/submissions/7a7ac79a-e1e1-4c07-87ca-e93080aa72e5

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Analysis_paperExplicitHaarCore_eq_latticeCore_damped
import Theorems.Thm_FourierJacobi_Analysis_tendsto_latticeCore_paperE


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
open MeasureTheory Filter
open scoped Topology
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)
namespace FourierJacobi.Analysis
theorem _root_.solution
    (a b d : ℂ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hd₀ : inverseSqrt qK < ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    Tendsto (fun T => paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE qK a b d)) := by
  apply (tendsto_latticeCore_paperE qK a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁).congr'
  filter_upwards [self_mem_nhdsWithin] with T hT
  rw [paperExplicitHaarCore_eq_latticeCore_damped K a b d T hq ha hb
    hT.1 hT.2 hd₀.le hd₁ π hπ]
end FourierJacobi.Analysis
