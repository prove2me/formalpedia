-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChartIntegralLocal.step_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:07.846071+00:00
-- url     : https://prove2.me/submissions/0df0a7c8-e50f-42b6-b474-558697c21197

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChartIntegralLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.ChartIntegralLocal
theorem _root_.solution {b : Bool} {X : Mat k r} (hX : inLie k r X) (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    {g : Mat k r} (hg : g ∈ GV k r) {ε : ℝ} (hε : 0 < ε)
    (hGm : ∀ t ∈ Metric.ball (0 : ℝ) ε, AEStronglyMeasurable (fun ξ => G ξ (cv b X t g)) μ)
    (hG'm : AEStronglyMeasurable (fun ξ => op b X (G ξ) g) μ)
    (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ ξ, ‖op b X (G ξ) (cv b X t g)‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ t ∈ Metric.ball (0 : ℝ) ε, Φ (cv b X t g) = ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ) :
    op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hε
  have h00 : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ε := Metric.mem_ball_self hε
  have hm0 : AEStronglyMeasurable (fun ξ => G ξ (cv b X 0 g)) μ := hGm 0 h00
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Metric.ball 0 ε) hs
    (Filter.mem_of_superset hs fun t ht => hψm.smul (hGm t ht))
    (hβ.mono' (hψm.smul hm0) (Eventually.of_forall fun ξ => (hsm ξ _).trans (by rw [cv_zero]; exact hb0 ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (by simp only [cv_zero]; exact hψm.smul hG'm)
    (Eventually.of_forall fun ξ t ht => (hsm ξ _).trans (hb1 t ht ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) =ᶠ[𝓝 0] fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ :=
    Filter.mem_of_superset hs fun t ht => hΦ t ht
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1.deriv_eq, key.2.deriv]
  simp only [cv_zero]
end Formalism.FourierDecayAlt.P.ChartIntegralLocal
