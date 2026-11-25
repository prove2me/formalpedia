-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Fk_integrable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:13:18.054086+00:00
-- url     : https://prove2.me/submissions/a9b241dd-4298-47e3-8fea-22df5da44aaa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_enorm_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
private theorem continuous_Fk_uncurry {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V}
    (hWc : Continuous W) : Continuous (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) := by
  have hσc := hσ.2.2.2 w
  unfold Fk
  refine Continuous.mul ?_ ?_
  · exact (hWc.comp (continuous_snd.snd.mul continuous_snd.fst)).inner (hWc.comp continuous_fst)
  · exact (hσc.comp continuous_fst).inner (hσc.comp (continuous_snd.snd.mul continuous_snd.fst))
private theorem lintegral_enorm_Fk_lt_infty {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hmeas : Measurable (fun x : G × G × G => ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ))
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS)) < ⊤ := by
  have hSae : ∀ᵐ q ∂μS, q ∈ S := by
    have h := compl_mem_ae_iff.2 hS0
    rw [compl_compl] at h
    exact h
  calc ∫⁻ x, ‖Fk σ w W x.1 x.2.1 x.2.2‖ₑ ∂(ν.prod (ν.prod μS))
      = ∫⁻ z, ∫⁻ y, ‖Fk σ w W z y.1 y.2‖ₑ ∂(ν.prod μS) ∂ν := lintegral_prod _ hmeas.aemeasurable
    _ = ∫⁻ z, ∫⁻ z', ∫⁻ q, ‖Fk σ w W z z' q‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_congr fun z => lintegral_prod _ (hmeas.comp measurable_prodMk_left).aemeasurable
    _ ≤ ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν :=
        lintegral_mono fun z => lintegral_mono fun z' => lintegral_mono_ae (by
          filter_upwards [hSae] with q hq
          exact Fk_enorm_le hσ w hWeq hτu z z' hq)
    _ < ⊤ := hconv
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G}
    {μS ν : Measure G} [SFinite μS] [SFinite ν] (hS0 : μS Sᶜ = 0) {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W)
    (hconv : ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν < ⊤) :
    Integrable (fun x : G × G × G => Fk σ w W x.1 x.2.1 x.2.2) (ν.prod (ν.prod μS)) := by
  have hcont := continuous_Fk_uncurry hσ w hWc
  exact ⟨hcont.aestronglyMeasurable,
    lintegral_enorm_Fk_lt_infty hσ w hS0 hWeq hτu (continuous_enorm.measurable.comp hcont.measurable) hconv⟩
end Formalism.L2.S.Pv.EnergyAbs
