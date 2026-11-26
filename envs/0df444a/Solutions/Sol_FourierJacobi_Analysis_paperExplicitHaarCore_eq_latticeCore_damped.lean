-- Prove2me | solution 1 for FourierJacobi.Analysis.paperExplicitHaarCore_eq_latticeCore_damped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:48.791435+00:00
-- url     : https://prove2.me/submissions/5e004185-84aa-4416-9cb8-ccff8a8993a9

import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Definitions.Def_FourierJacobi_Analysis_HaarLimits
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_paperExplicitHaarCore_eq_latticeCore


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
    (π : Kˣ) (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d T π = latticeCore qK a b d T := by
  apply paperExplicitHaarCore_eq_latticeCore K a b d T hq ha hb hT₀ hT₁.le hd₀ hd₁ ?_ π hπ
  have ht := inverseSqrt_pos (show 1 < qK by linarith)
  nlinarith
end FourierJacobi.Analysis
