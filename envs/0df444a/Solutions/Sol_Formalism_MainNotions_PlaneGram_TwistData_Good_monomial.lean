-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Good.monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:04:49.240235+00:00
-- url     : https://prove2.me/submissions/2dba2e7d-3776-41fb-8700-d9829807d0c2

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
namespace Good
theorem _root_.solution {p : ℕ} {ζ : D.EM} (h : D.GoodE p ζ) (c : K) : D.Good p (monomial ζ c) := by
  classical
  intro ζ' hζ'
  have := support_monomial_subset hζ'
  rw [Finset.mem_singleton] at this
  rw [this]; exact h
end Good
end Formalism.MainNotions.PlaneGram.TwistData
