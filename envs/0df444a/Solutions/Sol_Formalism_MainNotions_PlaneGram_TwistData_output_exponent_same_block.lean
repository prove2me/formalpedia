-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.output_exponent_same_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:14.751252+00:00
-- url     : https://prove2.me/submissions/13d1bb36-7925-4461-8ba8-10a124dab140

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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : eOut D.outP ζ' = eOut D.outP ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, hlab, htp⟩ := hb
  ext ⟨i, a⟩
  simp only [eOut, Finsupp.filter_apply]
  split_ifs with h
  · rcases i with b | t | t | t
    · exact absurd h (by simp [outB])
    · exact hlab t a
    · exact absurd h (by simp [outB])
    · exact htp t a
  · rfl
end Formalism.MainNotions.PlaneGram.TwistData
