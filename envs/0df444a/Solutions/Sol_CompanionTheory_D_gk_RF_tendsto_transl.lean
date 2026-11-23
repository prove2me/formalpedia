-- Prove2me | solution 1 for CompanionTheory.D.gk.RF.tendsto_transl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:24.314061+00:00
-- url     : https://prove2.me/submissions/18f0702e-e8ed-4f11-b38f-ab91c9ff27b1

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_CompactIntegralBoundedByQuotientNorm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_FundamentalDomainCusps_IntegrableMulBc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Filter BoundedContinuousFunction
open scoped ENNReal
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.RF
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
namespace CompanionTheory.D.gk.RF
theorem _root_.solution {φ : G → ℂ} (hφ : Integrable φ μ) :
    Tendsto (fun u => ∫ y, ‖φ y - φ (u * y)‖ ∂μ) (𝓝 1) (𝓝 0) := by
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  let f : Lp ℂ 1 μ := hφ.toL1 φ
  have hc : Continuous fun u : G => DomMulAct.mk u • f := (DomMulAct.continuous_mk).smul continuous_const
  have h1 : Tendsto (fun u : G => ‖f - DomMulAct.mk u • f‖) (𝓝 1) (𝓝 0) := by
    have := (continuous_const.sub hc (f := fun _ => f)).norm.tendsto 1
    simpa using this
  refine h1.congr fun u => ?_
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  have h2 := (measurePreserving_mul_left μ u).quasiMeasurePreserving.ae hφ.coeFn_toL1
  filter_upwards [Lp.coeFn_sub f (DomMulAct.mk u • f), DomMulAct.smul_Lp_ae_eq (DomMulAct.mk u) f, hφ.coeFn_toL1, h2]
    with y a b c d
  rw [a, Pi.sub_apply, b, c]
  simp only [Equiv.symm_apply_apply, smul_eq_mul]
  rw [d]
end CompanionTheory.D.gk.RF
