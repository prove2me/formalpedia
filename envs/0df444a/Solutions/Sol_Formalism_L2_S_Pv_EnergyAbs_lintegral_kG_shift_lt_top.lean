-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.lintegral_kG_shift_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:38:27.232893+00:00
-- url     : https://prove2.me/submissions/d0a424b2-8e8b-421f-9f74-cd2d2f145539

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_lintegral_four
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_measurable_bInt
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_ae_mem_four
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_enorm_kG_shift_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem ae_enorm_kG_le_bInt {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) {μ : Measure G} {d : ℝ}
    {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S τ ν W) (hW' : Formalism.L2.SG.Pf.EnergyAbs.IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0)
    (γ : G) :
    ∀ᵐ p ∂((ν.prod μS).prod (ν'.prod μS')),
      ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ≤
        ‖(d : ℂ)‖ₑ * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2 := by
  have hmem := ae_mem_four (ν := ν) (ν' := ν') h0 h0'
  refine hmem.mono fun p hp => ?_
  exact enorm_kG_shift_le hσ hW hW' hinv hinv' γ p.1.1 p.1.2 p.2.1 p.2.2 hp.1 hp.2
private theorem measurable_bInt_prod {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH)
    {W : G → V} {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) :
    Measurable (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) := by
  obtain ⟨-, hmul, -, hc⟩ := hσ
  have e : (fun p : (G × G) × (G × G) => bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2) =
      fun p => ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ * ‖W p.1.1‖ₑ * ‖W' p.2.1‖ₑ := by
    funext p
    unfold bInt
    rw [hmul (p.1.2 * γ * p.2.2⁻¹) p.2.1, ContinuousLinearMap.mul_apply]
  rw [e]
  have hg : Continuous fun p : (G × G) × (G × G) => p.1.2 * γ * p.2.2⁻¹ * p.2.1 := by fun_prop
  have h1 : Measurable fun p : (G × G) × (G × G) =>
      ‖⟪σ p.1.1 w, σ (p.1.2 * γ * p.2.2⁻¹ * p.2.1) w⟫_ℂ‖ₑ :=
    (continuous_enorm.comp
      (((hc w).comp (continuous_fst.comp continuous_fst)).inner ((hc w).comp hg))).measurable
  have h2 : Measurable fun p : (G × G) × (G × G) => ‖W p.1.1‖ₑ :=
    (continuous_enorm.comp (hW.comp (continuous_fst.comp continuous_fst))).measurable
  have h3 : Measurable fun p : (G × G) × (G × G) => ‖W' p.2.1‖ₑ :=
    (continuous_enorm.comp (hW'.comp (continuous_fst.comp continuous_snd))).measurable
  exact (h1.mul h2).mul h3
set_option maxHeartbeats 800000 in

private theorem lintegral_const_mul_bInt_eq_iterated {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS]
    [SFinite ν'] [SFinite μS'] {σ : G → (HH →L[ℂ] HH)} (hσ : Formalism.L2.SG.Pf.EnergyAbs.IsUnitRep σ) (w : HH) {W : G → V}
    {W' : G → V'} (hW : Continuous W) (hW' : Continuous W') (γ : G) (c : ℝ≥0∞) :
    ∫⁻ p : (G × G) × (G × G), c * bInt σ w W W' γ p.1.1 p.2.1 p.1.2 p.2.2
        ∂((ν.prod μS).prod (ν'.prod μS')) =
      c * ∫⁻ z : G, ∫⁻ z' : G, ∫⁻ s : G, ∫⁻ s' : G, bInt σ w W W' γ z z' s s'
        ∂μS' ∂μS ∂ν' ∂ν := by
  have hc := measurable_bInt_prod hσ w hW hW' γ
  have e1 := lintegral_const_mul (μ := (ν.prod μS).prod (ν'.prod μS')) c hc
  have e2 := lintegral_four (ν := ν) (μS := μS) (ν' := ν') (μS' := μS')
    (bInt σ w W W' γ) (measurable_bInt hσ w hW hW' γ)
  exact e1.trans (congrArg (fun x => c * x) e2)
end Formalism.L2.S.Pv.EnergyAbs
end
end

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
theorem _root_.solution {ν μS ν' μS' : Measure G} [SFinite ν] [SFinite μS] [SFinite ν'] [SFinite μS']
    {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ : Measure G} {d : ℝ} {w : HH} {S S' : Set G}
    {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (γ : G)
    (hB : ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', bInt σ w W W' γ z z' s s' ∂μS' ∂μS ∂ν' ∂ν < ⊤) :
    ∫⁻ p, ‖kG σ d w W W' γ (p.1.2⁻¹ * p.1.1, p.2.2⁻¹ * p.2.1)‖ₑ ∂((ν.prod μS).prod (ν'.prod μS')) < ⊤ := by
  have hle := ae_enorm_kG_le_bInt hσ hW hW' hinv hinv' h0 h0' γ
  have h2 := lintegral_const_mul_bInt_eq_iterated (ν := ν) (μS := μS) (ν' := ν') (μS' := μS') hσ w
    hW.2.2.2.2.1 hW'.2.2.2.2.1 γ ‖(d : ℂ)‖ₑ
  have hd : ‖(d : ℂ)‖ₑ ≠ ⊤ := enorm_ne_top
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [h2]
  exact (ENNReal.mul_ne_top hd hB.ne).lt_top
end Formalism.L2.S.Pv.EnergyAbs
