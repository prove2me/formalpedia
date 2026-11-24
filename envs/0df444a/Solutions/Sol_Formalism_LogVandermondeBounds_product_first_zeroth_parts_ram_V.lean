-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.ram_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:29:14.327589+00:00
-- url     : https://prove2.me/submissions/c287a0fc-cb09-4bba-a161-243ec1c78f2d

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_ne_zero_of_pair_eq_one
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_nmP_opU
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_trV_eq_zero
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_DU_formula

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
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ} {R : Type*} [CommRing R]
    (ψ : (Fin r → k) → R) (h : ∀ y, y ≠ 0 → nmV ψ y = 0) :
    (∀ f, nmP (opU ψ) f = 0) ∧ trV ψ = 0 ∧
      (2 ≤ r → ∀ x, x ≠ 0 → opD (opU ψ) x = ((Fintype.card k : R)) ^ (r - 1) * ψ x) := by
  have htr := trV_eq_zero ψ h
  refine ⟨fun f => ?_, htr, fun hr x hx => ?_⟩
  · rw [nmP_opU]
    exact Finset.sum_eq_zero (fun x hx =>
      h x (ne_zero_of_pair_eq_one (by simpa using hx)))
  · rw [DU_formula hr ψ x hx, h x hx, htr]; ring
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
