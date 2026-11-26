-- Prove2me | solution 1 for FourierJacobi.Analysis.explicit_haar_core_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:03:18.262884+00:00
-- url     : https://prove2.me/submissions/dee38567-0e1e-4c86-aa57-6f42cd266c04

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_integrable_undamped
import Theorems.Thm_FourierJacobi_Analysis_paperExplicitHaarCore_eq_paperE
import Theorems.Thm_FourierJacobi_Analysis_tendsto_paperExplicitHaarCore_paperE
import Theorems.Thm_FourierJacobi_Analysis_paper_denominator_interior_ne_zero


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
    (∀ r : Fin 3, Integrable
      (explicitCoreIntegrand K qK a b d 1 (coreCentral K π r)) (paperCoreMeasure K)) ∧
    paperExplicitHaarCore K a b d 1 π = paperE qK a b d ∧
    paperC qK * paperD1 qK a b d * paperD2 qK a b d ≠ 0 ∧
    Tendsto (fun T => paperExplicitHaarCore K a b d T π)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (paperE qK a b d)) := by
  exact ⟨explicitCoreIntegrand_integrable_undamped K a b d hq ha hb hd₀ hd₁ π hπ,
    paperExplicitHaarCore_eq_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ,
    paper_denominator_interior_ne_zero qK (by linarith) a b d ha hb hd₀ hd₁,
    tendsto_paperExplicitHaarCore_paperE K a b d hq ha hb hd₀ hd₁ ha₁ hb₁ hab hab₁ π hπ⟩
end FourierJacobi.Analysis
