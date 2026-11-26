-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_haar_special_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:48.90082+00:00
-- url     : https://prove2.me/submissions/c977d6c6-4563-4659-afd5-57a92e16629b

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Analysis_tendsto_positive_zero_product


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
theorem _root_.solution (a b : ℂ) (π : Kˣ) :
    Tendsto (fun T => ((1 - (1 : ℂ)) / ((qK : ℂ) + 1)) *
      paperExplicitHaarCore K a b (inverseSqrt qK : ℂ) T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 0) :=
  tendsto_positive_zero_product qK
    (fun T => paperExplicitHaarCore K a b (inverseSqrt qK : ℂ) T π)
end FourierJacobi.Analysis
