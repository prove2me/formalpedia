-- Prove2me | solution 1 for Formalism.ELL.isogeny_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:04.305859+00:00
-- url     : https://prove2.me/submissions/d62b927d-caf6-4d23-ac27-2bc6db660b83

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_QuadraticDifferenceHypotheses_expand_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL
open Formalism.ELL.QuadraticDifferenceHypotheses
universe u
namespace Formalism.ELL
theorem _root_.solution : IsoExpand.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t
  have E := expand_mk h n m y t
  rw [← sub_eq_zero, ← map_sub] at E
  exact (QuotientAddGroup.eq_zero_iff _).mp E
end Formalism.ELL
