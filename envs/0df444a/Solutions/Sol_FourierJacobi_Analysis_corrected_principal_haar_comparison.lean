-- Prove2me | solution 1 for FourierJacobi.Analysis.corrected_principal_haar_comparison
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:17.15967+00:00
-- url     : https://prove2.me/submissions/ce138e5f-b4e7-4dd9-9908-d0cd447a67e8

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Analysis_paperExplicitHaarCore_eq_paperE
import Theorems.Thm_FourierJacobi_Analysis_tendsto_paperExplicitHaarCore_paperE

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
    (2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d 1 π =
      2 / ((qK : ℂ) + 1) * paperE qK a b d) ∧
    Tendsto (fun T => 2 / ((qK : ℂ) + 1) * paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((qK : ℂ) + 1) * paperE qK a b d)) := by
  exact ⟨congrArg (fun z => 2 / ((qK : ℂ) + 1) * z)
    (paperExplicitHaarCore_eq_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ),
    (tendsto_paperExplicitHaarCore_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ).const_mul _⟩
end FourierJacobi.Analysis
