-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.GoodE.good_exponent_same_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:12.254034+00:00
-- url     : https://prove2.me/submissions/3f336ebd-ad45-43d0-bb2d-8d31b5c2c124

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
namespace GoodE
theorem _root_.solution {p : ℕ} {ζ ζ' : D.EM} (h : D.GoodE p ζ) (hb : D.SameBlockAlt ζ ζ') : D.GoodE p ζ' := by
  unfold GoodE at h ⊢
  unfold SameBlockAlt at hb
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hl, hlab, htp⟩ := hb
  refine ⟨fun t a => ?_, fun j m hm a => ?_, fun b => (hl _).trans (h3 b), fun t => ?_,
    fun t => (hl _).le.trans (h5 t)⟩
  · rw [hlab]; exact h1 t a
  · rw [htp]; exact h2 j m hm a
  · simp only [hl]; exact h4 t
end GoodE
end Formalism.MainNotions.PlaneGram.TwistData
