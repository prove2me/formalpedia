-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.mk_nrm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:10.631603+00:00
-- url     : https://prove2.me/submissions/9b9c3ad8-3b46-484b-ae69-ac55689e36f6

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion

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
    (h : QuadHyp N bar nrm φ) (α : O) (s : M) :
    QuotientAddGroup.mk' N (φ (α • s)) = QuotientAddGroup.mk' N (nrm α • φ s) :=
  sub_eq_zero.mp (by rw [← map_sub]; exact (QuotientAddGroup.eq_zero_iff _).mpr (h.2.2.1 α s))
end Formalism.ELL.QuadraticDifferenceHypotheses
