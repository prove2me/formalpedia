-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.energyAbs_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:38.998392+00:00
-- url     : https://prove2.me/submissions/628916ed-c550-4466-a504-64d75929f8c7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolner
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEnergy
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsPoint
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsMain
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_continuous_hsA_Xop
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_folner_limit
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_folner_seq
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_lintegral_hsA_Xop
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_point_lower
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_tendsto_energy


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution : EnergyAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ _ HH _ _ _ σ d w V V' _ _ _ _ _ _ S S' μS μS' ν ν' τ τ' W W' C _ m h
    hσ hSch hw hS hS' hF hF' hν hν' hq hq' hW hW' hD hhm hOOi hB hC hC'
  haveI := hν
  haveI := hν'
  haveI : SigmaFinite μS := hS.2.2.2.2.1
  haveI : SigmaFinite μS' := hS'.2.2.2.2.1
  obtain ⟨Ω, hΩ, hΩF⟩ := folner_seq hS hF
  obtain ⟨Ω', hΩ', hΩF'⟩ := folner_seq hS' hF'
  have hlim := folner_limit hσ hSch hw hS hν hq hW hC Ω hΩ hΩF
  have hlim' := folner_limit hσ hSch hw hS' hν' hq' hW' hC' Ω' hΩ' hΩF'
  have hd : 0 < d := hSch.1
  set φn : ℕ → G → ℝ≥0∞ := fun n g => ENNReal.ofReal (hsA (Xop μS ν μS' ν' σ d w W W' (Ω n) (Ω' n) g))
    with hφn
  have hφm : ∀ n, Measurable (φn n) := fun n =>
    ENNReal.measurable_ofReal.comp (continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)).measurable
  set Fn : ℕ → C → ℝ≥0∞ := fun n c => (μS (Ω n) * μS' (Ω' n))⁻¹ *
    ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS with hFn
  have hpt : ∀ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ≤ liminf (fun n => Fn n c) atTop :=
    fun c => point_lower hσ hS hS' hq hq' hW hW' Ω Ω' hΩ hΩ' hΩF hΩF'
      (fun n => continuous_hsA_Xop hσ μS ν μS' ν' d w W W' (Ω n) (Ω' n)) (h c) (hB c)
  have hinner : ∀ n, Measurable (fun c => ∫⁻ s, ∫⁻ s', φn n (s * h c * s'⁻¹) ∂μS' ∂μS) := by
    intro n
    have h3 : Measurable (fun r : (C × G) × G => φn n (r.1.2 * h r.1.1 * r.2⁻¹)) :=
      (hφm n).comp (((measurable_snd.comp measurable_fst).mul (hhm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h3.lintegral_prod_right'.lintegral_prod_right'
  have hmeasF : ∀ n, Measurable (Fn n) := fun n => (hinner n).const_mul _
  have hint : ∀ n, ∫⁻ c, Fn n c ∂m = (μS (Ω n) * μS' (Ω' n))⁻¹ *
      ENNReal.ofReal (d * (∑ i, ‖yv μS ν σ w W (Ω n) (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖yv μS' ν' σ w W' (Ω' n) (stdOrthonormalBasis ℂ V' j)‖ ^ 2)) := by
    intro n
    rw [lintegral_const_mul _ (hinner n), ← hD (φn n) (hφm n), lintegral_hsA_Xop hSch]
  have htend := tendsto_energy hd (fun n => ⟨(hΩ n).2.2.1, (hΩ n).2.2.2⟩)
    (fun n => ⟨(hΩ' n).2.2.1, (hΩ' n).2.2.2⟩) hlim hlim'
  calc ∫⁻ c, ENNReal.ofReal (hsA (∫ x, rk1A (W x) (W' ((h c)⁻¹ * x)) ∂μ)) ∂m
      ≤ ∫⁻ c, liminf (fun n => Fn n c) atTop ∂m := lintegral_mono hpt
    _ ≤ liminf (fun n => ∫⁻ c, Fn n c ∂m) atTop := lintegral_liminf_le hmeasF
    _ = ENNReal.ofReal (1 / d) := by
        simp only [hint]
        exact htend.liminf_eq
end Formalism.L2.S.Pv.EnergyAbs
