-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:46:51.949582+00:00
-- url     : https://prove2.me/submissions/c5cbdb54-4989-40ea-87ad-fa1d4f735579

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_eventually_ne_zero_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_eps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open MeasureTheory Filter Topology Set Polynomial
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P.PBK
theorem _root_.solution (s : ℕ) (σ : ℂ) :
    ∀ᶠ x in cocompact ℂ, rhoR s σ x = (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have hlog : Tendsto (fun x : ℂ => Complex.log (1 - σ / (x + σ))) (cocompact ℂ) (𝓝 0) := by
    have h2 := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h2
  have hpos : 0 < Real.pi / ((s : ℝ) + 1) := by positivity
  have hsmall : ∀ᶠ x in cocompact ℂ, Complex.log (1 - σ / (x + σ)) ∈ Metric.ball (0 : ℂ) (Real.pi / ((s : ℝ) + 1)) :=
    hlog (Metric.ball_mem_nhds 0 hpos)
  filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ, hsmall] with x hx hlx
  rw [Metric.mem_ball, dist_zero_right] at hlx

  have hb : ‖Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ)‖ < Real.pi := by
    rw [norm_mul, Complex.norm_natCast]
    have hs1 : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) + 1 := by
      have : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
      linarith
    calc ‖Complex.log (1 - σ / (x + σ))‖ * ((s - 1 : ℕ) : ℝ)
        ≤ ‖Complex.log (1 - σ / (x + σ))‖ * ((s : ℝ) + 1) := mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
      _ < Real.pi / ((s : ℝ) + 1) * ((s : ℝ) + 1) := mul_lt_mul_of_pos_right hlx (by positivity)
      _ = Real.pi := by field_simp
  have him := Complex.abs_im_le_norm (Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ))
  have hw : x / (x + σ) = 1 - σ / (x + σ) := by
    field_simp [hx.2]
    ring
  unfold Formalism.FourierDecayAlt.P.PBK.rhoR Formalism.FourierDecayAlt.P.PBK.lamR
  have hlt := abs_lt.mp (lt_of_le_of_lt him hb)
  rw [hw, ← Complex.cpow_natCast, ← Complex.cpow_mul _ hlt.1 hlt.2.le]
end Formalism.FourierDecayAlt.P.PBK
