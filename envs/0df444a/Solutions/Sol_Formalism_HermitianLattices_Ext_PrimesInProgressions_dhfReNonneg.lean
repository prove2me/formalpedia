-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfReNonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:34:42.172378+00:00
-- url     : https://prove2.me/submissions/dd1819a0-df4d-46e8-9c03-c9859e93dbff

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (S : Multiset ℂ) (h : ∀ x ∈ S, 0 < x.re) :
    0 ≤ ((S.map (fun x : ℂ => 1 / x)).sum).re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Complex.add_re]
    have ha := h a (Multiset.mem_cons_self a S)
    have h1 : 0 ≤ (1 / a).re := by
      rw [one_div, Complex.inv_re]
      exact div_nonneg ha.le (Complex.normSq_nonneg a)
    exact add_nonneg h1 (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
