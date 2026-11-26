-- Prove2me | solution 1 for FourierJacobi.Analysis.paperExplicitHaarCore_eq_latticeCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:39.621127+00:00
-- url     : https://prove2.me/submissions/6b0abd9d-e86c-47d8-8ac2-91e984d4e59e

import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Theorems.Thm_FourierJacobi_Analysis_explicitHaarCoreShell_eq_centralLatticeCore
import Theorems.Thm_FourierJacobi_Analysis_centralLatticeCore_sum


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open MeasureTheory FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_25
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_26
attribute [local instance] FourierJacobi.Analysis._p2m_local_instance_bcb4d405dd_27
namespace FourierJacobi.Analysis
theorem _root_.solution
    (a b d : ℂ) (T : ℝ) (hq : 2 < qK) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hT₀ : 0 < T) (hT₁ : T ≤ 1) (hd₀ : inverseSqrt qK ≤ ‖d‖) (hd₁ : ‖d‖ ≤ 1)
    (hstrict : T * inverseSqrt qK < ‖d‖) (π : Kˣ)
    (hπ : localFieldValuation K (π : K) = (1 : WithTop ℤ)) :
    paperExplicitHaarCore K a b d T π = latticeCore qK a b d T := by
  unfold paperExplicitHaarCore explicitHaarCore
  simp_rw [explicitHaarCoreShell_eq_centralLatticeCore K a b d T hq ha hb
    hT₀ hT₁ hd₀ hd₁ hstrict π hπ]
  exact centralLatticeCore_sum qK a b d T
end FourierJacobi.Analysis
