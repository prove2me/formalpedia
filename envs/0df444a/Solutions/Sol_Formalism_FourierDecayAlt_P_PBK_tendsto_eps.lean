-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.tendsto_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:12:25.859309+00:00
-- url     : https://prove2.me/submissions/62ee0a79-47f8-4d74-a226-20cba430f934

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne

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
theorem _root_.solution (σ : ℂ) : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝 0) := by
  have h : Tendsto (fun x : ℂ => x + σ) (cocompact ℂ) (cocompact ℂ) :=
    (Homeomorph.addRight σ).map_cocompact.le
  have hinv : Tendsto Inv.inv (cocompact ℂ) (𝓝 (0 : ℂ)) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded
  have h2 := (hinv.comp h).const_mul σ
  simpa [div_eq_mul_inv] using h2
end Formalism.FourierDecayAlt.P.PBK
