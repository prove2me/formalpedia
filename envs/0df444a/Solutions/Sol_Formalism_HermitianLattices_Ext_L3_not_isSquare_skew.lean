-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.not_isSquare_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:03:31.203834+00:00
-- url     : https://prove2.me/submissions/edcdca5a-2549-4946-9def-f3b18dfc7784

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {w : K} (hw0 : w ≠ 0) (hw : star w = -w) :
    ¬ IsSquare (⟨w * w, (mem_cmF_iff K _).2 (by rw [star_mul', hw]; ring)⟩ : cmF K) := by
  rintro ⟨r, hr⟩
  have hr' : w * w = (r : K) * r := congrArg Subtype.val hr
  have hs : star (r : K) = r := star_coe_cmF K r
  have hw2 : ∀ c : K, w = c → star c = c → False := by
    intro c hc hc'
    apply hw0
    have e : w = -w := by rw [← hw, hc, hc']
    have e2 : (2 : K) * w = 0 := by linear_combination e
    exact (mul_eq_zero.1 e2).resolve_left two_ne_zero
  have hz : (w - r) * (w + r) = 0 := by linear_combination hr'
  rcases mul_eq_zero.1 hz with h | h
  · exact hw2 r (sub_eq_zero.1 h) hs
  · exact hw2 (-r) (eq_neg_of_add_eq_zero_left h) (by rw [star_neg, hs])
end Formalism.HermitianLattices.Ext.L3
