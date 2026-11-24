-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.digOK_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:05.30014+00:00
-- url     : https://prove2.me/submissions/9c83aa90-3a99-43f9-b443-08dfbb29e387

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory

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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (hDIG : DIG K v p) (hD : DVRHyp v p) (hc : 1 ≤ D.c) :
    ∃ cst gam, D.DigOK v p cst gam := by
  obtain ⟨cst, gam, h1, h2⟩ := hDIG hD D.Tau D.r D.g
  refine ⟨cst, gam, ?_⟩
  unfold DigOK
  exact ⟨h1, fun ρ hρ ε hε => h2 ρ hρ D.c hc ε hε⟩
end Formalism.MainNotions.PlaneGram.TwistData
