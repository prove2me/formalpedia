-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.nmP_eq_nmV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:11.704107+00:00
-- url     : https://prove2.me/submissions/69a7e6aa-5962-46e8-8967-ff5bc065c122

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity

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
theorem _root_.solution (φ : (Fin r → k) → R) : nmP φ = nmV φ := by
  funext f
  unfold nmP nmV diaP diaV
  exact (Fintype.sum_equiv (Equiv.inv kˣ) (fun c => φ (((c⁻¹ : kˣ) : k) • f))
    (fun c => φ ((c : k) • f)) (fun c => rfl)).symm
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
