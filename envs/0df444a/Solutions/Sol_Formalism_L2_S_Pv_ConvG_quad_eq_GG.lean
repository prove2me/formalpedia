-- Prove2me | solution 1 for Formalism.L2.S.Pv.ConvG.quad_eq_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:20:05.528479+00:00
-- url     : https://prove2.me/submissions/005b1d98-2928-482e-a1f5-9e322aeae311

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG
import Theorems.Thm_Formalism_L2_S_Pv_ConvG_weil_inv
import Theorems.Thm_Formalism_L2_S_Pv_ConvG_measurable_PhiGG
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_coef_shift


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
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
  {V V' : Type} [NormedAddCommGroup V] [NormedAddCommGroup V']
namespace Formalism.L2.S.Pv.ConvG
theorem _root_.solution {μ μS ν μS' ν' : Measure G} [SFinite μS] [SFinite ν] [SFinite μS'] [SFinite ν'] [SFinite μ]
    {S S' : Set G} {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} {W' : G → V'}
    (hWc : Continuous W) (hWc' : Continuous W')
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (hWe' : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS' ∂ν')
    (hinv : μS.map (fun x => x⁻¹) = μS) (hinv' : μS'.map (fun x => x⁻¹) = μS')
    (h0 : μS Sᶜ = 0) (h0' : μS' S'ᶜ = 0) (hiS : ∀ a ∈ S, a⁻¹ ∈ S) (hiS' : ∀ a ∈ S', a⁻¹ ∈ S')
    (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) (hWS' : ∀ s ∈ S', ∀ x, ‖W' (s * x)‖ = ‖W' x‖) (γ : G) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS ∂ν' ∂ν =
      ∫⁻ x, ∫⁻ y, PhiGG σ w W W' γ x y ∂μ ∂μ := by
  have hΦ := measurable_PhiGG hσ w hWc hWc' γ

  have hpt : ∀ z z' s s', s ∈ S → s' ∈ S' →
      ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ = PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') := by
    intro z z' s s' hs hs'
    unfold PhiGG
    rw [coef_shift hσ w γ z s z' s']
    have e1 : ‖W (s⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS _ (hiS s hs)]
    have e2 : ‖W' (s'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS' _ (hiS' s' hs')]
    rw [e1, e2]
  have haeS : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have haeS' : ∀ᵐ s ∂μS', s ∈ S' := by rw [ae_iff]; exact h0'
  have hin : ∀ z z', ∫⁻ s, ∫⁻ s', ‖⟪σ z w, σ (s * γ * s'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W' z'‖ₑ ∂μS' ∂μS =
      ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS := by
    intro z z'
    refine lintegral_congr_ae ?_
    filter_upwards [haeS] with s hs
    refine lintegral_congr_ae ?_
    filter_upwards [haeS'] with s' hs'
    exact hpt z z' s s' hs hs'
  simp only [hin]

  have hswap : ∀ z, ∫⁻ z', ∫⁻ s, ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂μS ∂ν' =
      ∫⁻ s, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS' ∂ν' ∂μS := by
    intro z
    have hm : Measurable (Function.uncurry fun z' s : G => ∫⁻ s', PhiGG σ w W W' γ (s⁻¹ * z) (s'⁻¹ * z') ∂μS') := by
      have hg : Measurable (fun q : (G × G) × G => ((q.1.2⁻¹ * z, q.2⁻¹ * q.1.1) : G × G)) :=
        (((measurable_snd.comp measurable_fst).inv.mul measurable_const)).prodMk
          ((measurable_snd.inv).mul (measurable_fst.comp measurable_fst))
      have h3 : Measurable (fun q : (G × G) × G => PhiGG σ w W W' γ (q.1.2⁻¹ * z) (q.2⁻¹ * q.1.1)) :=
        hΦ.comp hg
      exact h3.lintegral_prod_right'
    exact lintegral_lintegral_swap hm.aemeasurable
  simp only [hswap]

  have hy : ∀ a, ∫⁻ z', ∫⁻ s', PhiGG σ w W W' γ a (s'⁻¹ * z') ∂μS' ∂ν' = ∫⁻ y, PhiGG σ w W W' γ a y ∂μ := by
    intro a
    exact weil_inv hWe' hinv' (fun y => PhiGG σ w W W' γ a y) (hΦ.comp (measurable_const.prodMk measurable_id))
  simp only [hy]

  have hmy : Measurable (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) := hΦ.lintegral_prod_right'
  exact weil_inv hWe hinv (fun a => ∫⁻ y, PhiGG σ w W W' γ a y ∂μ) hmy
end Formalism.L2.S.Pv.ConvG
