-- Prove2me | solution 1 for Formalism.L2.S.Pv.ConvG.triple_lintegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:15:23.93337+00:00
-- url     : https://prove2.me/submissions/8b3e2842-395e-4b2e-81d1-f79597dc67a3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_ConvGGG
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_rep_mul_apply


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
theorem _root_.solution {μ μS ν : Measure G} [SFinite μS] [SFinite ν] {S : Set G} {σ : G → (HH →L[ℂ] HH)}
    (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    (hWe : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν)
    (h0 : μS Sᶜ = 0) (hWS : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖) :
    ∫⁻ z, ∫⁻ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS ∂ν ∂ν =
      ∫⁻ z, ‖W z‖ₑ * ∫⁻ y, ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ ∂μ ∂ν := by
  refine lintegral_congr fun z => ?_
  set H : G → ℝ≥0∞ := fun y => ‖⟪σ z w, σ y w⟫_ℂ‖ₑ * ‖W y‖ₑ with hHdef
  have hHm : Measurable H := by
    have h1 : Continuous (fun y => ⟪σ z w, σ y w⟫_ℂ) := Continuous.inner (𝕜 := ℂ) continuous_const (hσ.2.2.2 w)
    exact (h1.enorm.measurable).mul hWc.enorm.measurable
  have hae : ∀ᵐ s ∂μS, s ∈ S := by rw [ae_iff]; exact h0
  have hin : ∀ z', ∫⁻ s, ‖⟪σ z w, σ s (σ z' w)⟫_ℂ‖ₑ * ‖W z‖ₑ * ‖W z'‖ₑ ∂μS =
      ‖W z‖ₑ * ∫⁻ s, H (s * z') ∂μS := by
    intro z'
    rw [← lintegral_const_mul (‖W z‖ₑ) (f := fun s => H (s * z')) (hHm.comp (measurable_mul_const z'))]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with s hs
    simp only [hHdef]
    have e1 : σ s (σ z' w) = σ (s * z') w := (rep_mul_apply hσ s z' w)
    have e2 : ‖W z'‖ₑ = ‖W (s * z')‖ₑ := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hWS s hs z']
    rw [e1, e2]
    ring
  simp only [hin]
  have hmeas : Measurable (fun z' : G => ∫⁻ s, H (s * z') ∂μS) := by
    have h2 : Measurable (fun p : G × G => H (p.2 * p.1)) := hHm.comp (measurable_snd.mul measurable_fst)
    exact h2.lintegral_prod_right'
  rw [lintegral_const_mul (‖W z‖ₑ) (f := fun z' => ∫⁻ s, H (s * z') ∂μS) hmeas]
  congr 1
  exact (hWe H hHm).symm
end Formalism.L2.S.Pv.ConvG
