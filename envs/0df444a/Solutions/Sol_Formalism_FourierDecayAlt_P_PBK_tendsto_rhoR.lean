-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_rhoR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:22:56.505385+00:00
-- url     : https://prove2.me/submissions/4131f821-b688-4374-b746-52cdf178b400

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_tendsto_eps
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_rhoR_eq_eventually

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
theorem _root_.solution (s : ℕ) (σ : ℂ) : Tendsto (rhoR s σ) (cocompact ℂ) (𝓝 1) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have h2 : Tendsto (fun x : ℂ => (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)) (cocompact ℂ) (𝓝 1) := by
    have h3 := (continuousAt_cpow_const (b := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)
      (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h3
  exact h2.congr' ((Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ).mono fun x hx => hx.symm)
end Formalism.FourierDecayAlt.P.PBK
