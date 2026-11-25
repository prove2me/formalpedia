-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.quot_map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:00:32.490534+00:00
-- url     : https://prove2.me/submissions/ef8701ba-4ff2-4752-8531-7c2711487fcc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ μS ν : Measure G} [SFinite ν] [SFinite μS] (hq : IsQuot μ μS ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) :
    μ = (ν.prod μS).map (fun p => p.2⁻¹ * p.1) := by
  have hm : Measurable (fun p : G × G => p.2⁻¹ * p.1) := measurable_snd.inv.mul measurable_fst
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs)]
  have h := hq (s.indicator 1) (measurable_one.indicator hs)
  rw [lintegral_indicator_one hs] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have hx : MeasurableSet ((fun t : G => t * x) ⁻¹' s) := measurable_mul_const x hs
  have hx' : MeasurableSet ((fun t : G => t⁻¹ * x) ⁻¹' s) := (measurable_inv.mul_const x) hs
  calc ∫⁻ t, s.indicator (1 : G → ℝ≥0∞) (t * x) ∂μS
      = ∫⁻ t, ((fun t : G => t * x) ⁻¹' s).indicator (1 : G → ℝ≥0∞) t ∂μS := rfl
    _ = μS ((fun t : G => t * x) ⁻¹' s) := lintegral_indicator_one hx
    _ = (μS.map (fun t => t⁻¹)) ((fun t : G => t⁻¹ * x) ⁻¹' s) := by
        rw [Measure.map_apply measurable_inv hx']
        congr 1
        ext t
        simp
    _ = μS ((fun t : G => t⁻¹ * x) ⁻¹' s) := by rw [hinv]
    _ = _ := rfl
end Formalism.L2.S.Pv.EnergyAbs
