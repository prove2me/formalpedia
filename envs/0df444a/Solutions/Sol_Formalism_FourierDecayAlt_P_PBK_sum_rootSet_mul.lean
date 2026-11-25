-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBK.sum_rootSet_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:23:28.586829+00:00
-- url     : https://prove2.me/submissions/33c5dad2-cff4-442f-9824-6db0e000202b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RootPushforwardDensity
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_rootSet_mul_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_injOn_rootSet_mul

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
theorem _root_.solution {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0)
    (hz : z ^ s = w) (hρ : ρ ^ s = l) (hl : l ≠ 0) (Gf : ℂ → E) :
    ∑ y ∈ G.rootSet s (l * w), Gf y = ∑ ζ ∈ G.rootSet s 1, Gf (ζ * ρ * z) := by
  rw [Formalism.FourierDecayAlt.P.PBK.rootSet_mul_eq hs hw hz hρ hl,
    Finset.sum_image fun x hx y hy h => Formalism.FourierDecayAlt.P.PBK.injOn_rootSet_mul hs hw hz hρ hl hx hy h]
end Formalism.FourierDecayAlt.P.PBK
