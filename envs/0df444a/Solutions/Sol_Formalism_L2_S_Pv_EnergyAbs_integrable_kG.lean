-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.integrable_kG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:53:21.146365+00:00
-- url     : https://prove2.me/submissions/689e63a4-e82c-4ed3-8efa-9d3424c923aa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Theorems.Thm_P2M_Formalism_L2_S_Pv_EnergyAbs_continuous__inv_dfd26146d176
import Theorems.Thm_P2M_Formalism_L2_S_Pv_EnergyAbs_prod_map__inv_221c0b6c8f4d
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_lintegral_kG_shift_lt_top
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_continuous_kG


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
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (hm : μ = (ν.prod μS).map φinv) (hm' : μ = (ν'.prod μS').map φinv) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    Integrable (kG σ d w W W' γ) (μ.prod μ) := by
  have hK : Continuous (kG σ d w W W' γ) :=
    continuous_kG hσ d w hW.2.2.2.2.1 hW'.2.2.2.2.1 γ
  refine ⟨hK.aestronglyMeasurable, ?_⟩
  have hF : Measurable (Prod.map φinv φinv : (G × G) × (G × G) → G × G) :=
    (continuous_φinv.prodMap continuous_φinv).measurable
  have hg : Measurable fun q : G × G => ‖kG σ d w W W' γ q‖ₑ :=
    (continuous_enorm.comp hK).measurable
  show ∫⁻ q, ‖kG σ d w W W' γ q‖ₑ ∂(μ.prod μ) < ⊤
  rw [prod_map_φinv hm hm', lintegral_map hg hF]
  exact lintegral_kG_shift_lt_top hσ hW hW' hinv hinv' h0 h0' γ hB
end Formalism.L2.S.Pv.EnergyAbs
