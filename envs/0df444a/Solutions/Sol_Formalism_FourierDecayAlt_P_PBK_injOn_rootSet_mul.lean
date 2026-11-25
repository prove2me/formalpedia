-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.injOn_rootSet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:01:12.796062+00:00
-- url     : https://prove2.me/submissions/1ecf3e01-b066-4c70-922f-b687706911c3

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
theorem _root_.solution {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : Set.InjOn (fun ζ => ζ * ρ * z) (G.rootSet s 1 : Set ℂ) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  intro ζ _ ζ' _ h
  exact mul_right_cancel₀ hρ0 (mul_right_cancel₀ hz0 h)
end Formalism.FourierDecayAlt.P.PBK
