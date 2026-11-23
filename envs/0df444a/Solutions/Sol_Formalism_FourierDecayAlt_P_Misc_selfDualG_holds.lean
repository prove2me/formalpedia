-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Misc.selfDualG_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:06.483422+00:00
-- url     : https://prove2.me/submissions/8abd0df3-acb9-4da1-a1ba-c808f552b466

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Misc
open Formalism.FourierDecayAlt.I Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Misc
theorem _root_.solution : SelfDualG := by
  intro F _ o q hq hq0 a
  constructor
  · intro h
    have h1 := h (1, 1) ⟨o.one_mem, o.one_mem, 0, o.zero_mem, by simp⟩
    have h2 := h (q, 0) ⟨hq, o.zero_mem, 1, o.one_mem, by simp⟩
    simp only [mul_one, mul_zero, sub_zero] at h1 h2
    have e2 : a.1 * q / q = a.1 := by field_simp
    rw [e2] at h2
    refine ⟨h2, ?_, (a.1 - a.2) / q, h1, by field_simp⟩
    have : a.2 = a.1 - q * ((a.1 - a.2) / q) := by field_simp; ring
    rw [this]; exact o.sub_mem h2 (o.mul_mem hq h1)
  · rintro ⟨ha1, ha2, s, hs, has⟩ b ⟨hb1, hb2, t, ht, hbt⟩
    have ha : a.1 = a.2 + q * s := by linear_combination has
    have hb : b.1 = b.2 + q * t := by linear_combination hbt
    have e : (a.1 * b.1 - a.2 * b.2) / q = a.2 * t + s * b.2 + q * s * t := by
      rw [ha, hb]; field_simp; ring
    rw [e]
    exact o.add_mem (o.add_mem (o.mul_mem ha2 ht) (o.mul_mem hs hb2)) (o.mul_mem (o.mul_mem hq hs) ht)
end Formalism.FourierDecayAlt.P.Misc
