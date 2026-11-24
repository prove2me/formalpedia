-- Prove2me | solution 1 for Formalism.L2.DIV.conj_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:53:36.297381+00:00
-- url     : https://prove2.me/submissions/ddf84ad1-3924-4300-88e8-752aadcaebea

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
import Theorems.Thm_Formalism_L2_DIV_conj_ne_of_sq_neg
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostRaw_jOf_coe
import Theorems.Thm_Formalism_L2_Host_algC_coe
import Theorems.Thm_Formalism_L2_Host_jOf_coe
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.HC.HostRaw.jOf_coe
attribute [local simp] Formalism.L2.Host.algC_coe
attribute [local simp] Formalism.L2.Host.jOf_coe
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution {w : ℂ} {r : ℝ} (hw : w ^ 2 = (r : ℂ)) :
    starRingEnd ℂ w = (if r < 0 then -1 else 1) * w := by
  have h2 : (starRingEnd ℂ w) ^ 2 = w ^ 2 := by rw [← map_pow, hw, Complex.conj_ofReal]
  split_ifs with hr
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact absurd h (conj_ne_of_sq_neg hr hw)
    · rw [h]; ring
  · rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · rw [h]; ring
    · have hre : w.re = 0 := by
        have := congrArg Complex.re h
        simp at this
        linarith
      have him : w.im = 0 := by
        have := congrArg Complex.re hw
        rw [sq, Complex.mul_re, hre, Complex.ofReal_re] at this
        have h0 : w.im * w.im ≤ 0 := by have := not_lt.1 hr; linarith
        nlinarith [mul_self_nonneg w.im]
      have hw0 : w = 0 := Complex.ext hre him
      rw [hw0]; simp
end Formalism.L2.DIV
