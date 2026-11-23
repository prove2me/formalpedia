-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.biHyp_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:21:54.919679+00:00
-- url     : https://prove2.me/submissions/383f8546-72fc-4873-9559-396fdc7bdd7f

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_mk_quadDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution {N : AddSubgroup T} {bar : O → O} {nrm : O → S} {φ : M → T}
    (h : QuadHyp N bar nrm φ) : BiHyp bar (fun a => QuotientAddGroup.mk' N (φ a)) := by
  have key : ∀ x : T, x ∈ N → QuotientAddGroup.mk' N x = 0 :=
    fun x hx => (QuotientAddGroup.eq_zero_iff x).mpr hx
  refine ⟨?_, key _ h.2.1, ?_⟩
  · intro a a' b
    have := key _ (h.1 a a' b)
    simp only [map_sub, mk_quadDiff] at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · intro α a b
    have := key _ (h.2.2.2 α a b)
    simp only [map_sub, mk_quadDiff] at this
    exact sub_eq_zero.mp this
end Formalism.ELL.QuadraticDifferenceHypotheses
