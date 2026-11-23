-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.opU_eq_opD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:33.713403+00:00
-- url     : https://prove2.me/submissions/20767783-003d-42c2-9972-86fc50847901

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (ψ : (Fin r → k) → R) : opU ψ = opD ψ := by
  funext f
  unfold opU opD
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [pair_comm]
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
