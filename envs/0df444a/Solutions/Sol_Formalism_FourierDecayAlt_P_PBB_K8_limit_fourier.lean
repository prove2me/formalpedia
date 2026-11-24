-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.limit_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:50:21.494162+00:00
-- url     : https://prove2.me/submissions/a6cdbe67-f877-47b1-a0fa-5452c910d4b5

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_dw_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_bound_all
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_fourier_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBB_K8_ae_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution (g : ℕ → ℂ → ℂ) (g0 : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) (C C' : ℝ)
    (hφc : ∀ n, Continuous (φ n)) (hφg : ∀ n c, c ≠ 0 → φ n c = g n c)
    (hconv : ∀ c, Tendsto (fun n => g n c) atTop (𝓝 (g0 c)))
    (hb : ∀ n c, c ≠ 0 → ‖g n c‖ ≤ C * dw c)
    (hT : ∀ n w, ‖𝓕 (φ n) w‖ ≤ C' * dw w) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧ (∀ c, c ≠ 0 → ψ c = g0 c) ∧ (∀ c, ‖ψ c‖ ≤ C * dw c) ∧
      Tendsto (fun n => ∫ c, φ n c) atTop (𝓝 (∫ c, ψ c)) := by
  have hφb : ∀ n c, ‖φ n c‖ ≤ C * dw c := fun n =>
    bound_all (hφc n) fun c hc => by rw [hφg n c hc]; exact hb n c hc
  have hBi : Integrable (fun c => C * dw c) := dw_integrable.const_mul C
  have hB'i : Integrable (fun c => C' * dw c) := dw_integrable.const_mul C'
  have hφi : ∀ n, Integrable (φ n) := fun n =>
    hBi.mono' (hφc n).aestronglyMeasurable (Eventually.of_forall (hφb n))
  have hFt : ∀ w, Tendsto (fun n => 𝓕 (φ n) w) atTop (𝓝 (𝓕 g0 w)) := by
    intro w
    show Tendsto (fun n => ∫ v, 𝐞 (-⟪v, w⟫) • φ n v) atTop (𝓝 (∫ v, 𝐞 (-⟪v, w⟫) • g0 v))
    refine tendsto_integral_of_dominated_convergence (fun c => C * dw c) (fun n => ?_) hBi (fun n => ?_) ?_
    · exact ((Real.fourierIntegral_convergent_iff w).mpr (hφi n)).aestronglyMeasurable
    · exact Eventually.of_forall fun c => by rw [Circle.norm_smul]; exact hφb n c
    · filter_upwards [ae_ne_zero] with c hc
      simp only [hφg _ c hc]
      exact (hconv c).const_smul _
  have hGm : AEStronglyMeasurable (𝓕 g0) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (fourier_cont (hφi n)).aestronglyMeasurable)
      (ae_of_all _ hFt)
  have hGb : ∀ w, ‖𝓕 g0 w‖ ≤ C' * dw w := fun w => le_of_tendsto' (hFt w).norm fun n => hT n w
  have hGi : Integrable (𝓕 g0) := hB'i.mono' hGm (Eventually.of_forall hGb)
  have hinv : ∀ n, 𝓕⁻ (𝓕 (φ n)) = φ n := fun n =>
    (hφc n).fourierInv_fourier_eq (hφi n)
      (hB'i.mono' (fourier_cont (hφi n)).aestronglyMeasurable (Eventually.of_forall (hT n)))
  set ψ : ℂ → ℂ := 𝓕⁻ (𝓕 g0) with hψ
  have hψlim : ∀ c, Tendsto (fun n => φ n c) atTop (𝓝 (ψ c)) := by
    intro c
    have : (fun n => φ n c) = fun n => 𝓕⁻ (𝓕 (φ n)) c := funext fun n => by rw [hinv n]
    rw [this, hψ]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun w => C' * dw w) (fun n => ?_) hB'i (fun n => ?_) ?_
    · exact ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
        (fourier_cont (hφi n))).aestronglyMeasurable
    · exact Eventually.of_forall fun w => by rw [Circle.norm_smul]; exact hT n w
    · exact ae_of_all _ fun w => (hFt w).const_smul _
  refine ⟨ψ, ?_, fun c hc => ?_, fun c => le_of_tendsto' (hψlim c).norm fun n => hφb n c, ?_⟩
  · have : ψ = fun c => 𝓕 (𝓕 g0) (-c) := funext fun c => Real.fourierInv_eq_fourier_neg _ c
    rw [this]
    exact (fourier_cont hGi).comp continuous_neg
  · refine tendsto_nhds_unique (hψlim c) ?_
    have : (fun n => φ n c) = fun n => g n c := funext fun n => hφg n c hc
    rw [this]
    exact hconv c
  · exact tendsto_integral_of_dominated_convergence (fun c => C * dw c)
      (fun n => (hφc n).aestronglyMeasurable) hBi (fun n => ae_of_all _ (hφb n)) (ae_of_all _ hψlim)
end Formalism.FourierDecayAlt.P.PBB.K8
