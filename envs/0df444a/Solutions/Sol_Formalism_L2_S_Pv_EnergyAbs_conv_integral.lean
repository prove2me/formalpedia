-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.conv_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:27.394697+00:00
-- url     : https://prove2.me/submissions/faf2f3aa-ee69-4ad1-a7ce-cc752513a720

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cnt_measurable
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_cnt_le
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_conv_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set G} {μS : Measure G} [SFinite μS]
    (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hfin : μS Ω < ⊤) (f : G → E)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω))) :
    ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS = ∫ q, (cnt μS Ω q).toReal • f q ∂μS := by
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  have hI : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω)) := by
    assumption
  have h1 : ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS
      = ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω)) :=
    (integral_prod (fun p : G × G => f (p.1 * p.2⁻¹)) hI).symm
  have h2 : ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω))
      = ∫ q, f q ∂(((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹)) :=
    (integral_map_of_stronglyMeasurable hg hf).symm
  rw [h1, h2, conv_map hS hΩm hΩS]
  exact integral_withDensity_eq_integral_toReal_smul (cnt_measurable hΩm)
    (ae_of_all _ fun q => (cnt_le μS Ω q).trans_lt hfin) f
end Formalism.L2.S.Pv.EnergyAbs
