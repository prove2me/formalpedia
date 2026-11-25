-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ChOK.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:06:54.097381+00:00
-- url     : https://prove2.me/submissions/d2149bcd-839f-4dca-8031-a8d3f78f8527

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
namespace Formalism.MainNotions.PlaneGram.TwistData
namespace ChOK
theorem _root_.solution {θ θ' : (j : Fin D.J) → Fin (D.nch j) → ℝ} {a : ℝ}
    {G : MvPolynomial (D.OL × Fin D.r) K} (h : D.ChOK v p θ a G) (hθ : ∀ j i, θ' j i ≤ θ j i) :
    D.ChOK v p θ' a G := by
  obtain ⟨G0, E, h1, h2, h3, h4⟩ := h
  exact ⟨G0, E, h1, h2, h3, fun ρ j i => vala_mono (hθ j i) (h4 ρ j i)⟩
end ChOK
end Formalism.MainNotions.PlaneGram.TwistData
