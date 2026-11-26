-- Prove2me | solution 1 for FourierJacobi.Analysis.explicitCoreIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:57:46.605124+00:00
-- url     : https://prove2.me/submissions/d85e73ec-ff4c-4212-addd-33c840a2fa84

import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
import Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
import Theorems.Thm_FourierJacobi_Analysis_coreIntegralPrefactor_ne_zero
import Theorems.Thm_FourierJacobi_Analysis_integrable_prefactor_core_eq_centralLatticeCore

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
    (hstrict : T * inverseSqrt qK < ‖d‖) (r : Fin 3) (z : K)
    (hz : CentralRepresentative K (r.val : ℤ) z) :
    Integrable (explicitCoreIntegrand K qK a b d T z) (paperCoreMeasure K) := by
  have hi := (integrable_prefactor_core_eq_centralLatticeCore K a b d T hq ha hb
    hT₀ hT₁ hd₀ hd₁ hstrict r z hz).1
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr
    (coreIntegralPrefactor_ne_zero qK (by linarith) r)) _).mp hi
end FourierJacobi.Analysis
