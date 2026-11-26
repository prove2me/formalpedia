-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitCoreIntegrand_integrable_damped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:08.540807+00:00
-- url     : https://prove2.me/submissions/dd3b684d-4742-4551-bf10-fa5b7cdeaf09

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_centralRepresentative_coreCentral
import Theorems.Thm_FourierJacobi_Analysis_explicitCoreIntegrand_integrable


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
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T < 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) (r : Fin 3) :
    Integrable (explicitCoreIntegrand K qK a b d T (coreCentral K π r))
      (paperCoreMeasure K) := by
  apply explicitCoreIntegrand_integrable K a b d T hq ha hb hT₀ hT₁.le hd₀ hd₁ ?_
    r (coreCentral K π r) (centralRepresentative_coreCentral K π hπ r)
  have ht := inverseSqrt_pos (show 1 < qK by linarith)
  nlinarith
end FourierJacobi.Analysis
