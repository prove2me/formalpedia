-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:28.857056+00:00
-- url     : https://prove2.me/submissions/f5b922a9-10f0-45b1-aa74-2443893f8341

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial

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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (x : D.ML × Fin D.r) :
    D.ph p (X x : MvPolynomial (D.ML × Fin D.r) K) = monomial (D.varE p x) 1 := by
  obtain ⟨i, a⟩ := x
  unfold ph
  rw [aeval_X]
  rcases i with b | t | t | t <;> simp [varE, X, monomial_pow]
end Formalism.MainNotions.PlaneGram.TwistData
