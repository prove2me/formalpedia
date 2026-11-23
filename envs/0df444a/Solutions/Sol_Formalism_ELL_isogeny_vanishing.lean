-- Prove2me | solution 1 for Formalism.ELL.isogeny_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:01.407944+00:00
-- url     : https://prove2.me/submissions/73ae4e2c-8855-4a54-b609-66bf1c3af33a

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion
import Theorems.Thm_Formalism_ELL_isogeny_expansion

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
theorem _root_.solution : IsoVanish.{u} := by
  intro O S M T _ _ _ _ _ _ N bar nrm φ h n m y t hiso hnrm
  have E := isogeny_expansion O S M T N bar nrm φ h n m y t
  have hz : ∀ a : M, quadDiff φ a 0 ∈ N := fun a => by
    simpa [quadDiff] using neg_mem h.2.1
  simp only [hiso, hnrm, zero_smul, Finset.sum_const_zero, zero_add] at E
  have hS : (∑ e, ∑ e' ∈ Finset.univ.filter (fun e' => e < e'), quadDiff φ (t e) 0) ∈ N :=
    sum_mem fun e _ => sum_mem fun e' _ => hz _
  have := add_mem E hS
  rwa [sub_add_cancel] at this
end Formalism.ELL
