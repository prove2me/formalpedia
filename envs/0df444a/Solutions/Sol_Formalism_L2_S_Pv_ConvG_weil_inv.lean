-- Prove2me | solution 1 for Formalism.L2.S.Pv.ConvG.weil_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:49.699351+00:00
-- url     : https://prove2.me/submissions/ce16ec2c-e936-4c23-a1b7-2d89905e47f4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.ConvG
open Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
namespace Formalism.L2.S.Pv.ConvG
theorem _root_.solution {μ μS ν : Measure G} [SFinite μS] [SFinite ν]
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hinv : μS.map (fun x => x⁻¹) = μS) (Ψ : G → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z, ∫⁻ s, Ψ (s⁻¹ * z) ∂μS ∂ν = ∫⁻ x, Ψ x ∂μ := by
  rw [hW Ψ hΨ]
  refine lintegral_congr fun z => ?_
  have hm : Measurable (fun s : G => Ψ (s * z)) := hΨ.comp (measurable_id.mul measurable_const)
  conv_rhs => rw [← hinv]
  rw [lintegral_map hm measurable_inv]
end Formalism.L2.S.Pv.ConvG
