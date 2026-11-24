-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.comm_U
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:37:47.657707+00:00
-- url     : https://prove2.me/submissions/9beb3bcf-5563-41de-96fc-39971ba8edbf

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_RamifiedLatticeOperatorIdentity
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_smul_left
import Theorems.Thm_Formalism_LogVandermondeBounds_product_first_zeroth_parts_pair_smul_right

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
theorem _root_.solution (c : kˣ) (ψ : (Fin r → k) → R) : opU (diaV c ψ) = diaP c (opU ψ) := by
  funext f
  unfold opU diaV diaP
  refine Finset.sum_nbij' (fun x => ((c⁻¹ : kˣ) : k) • x) (fun y => (c : k) • y) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [pair_smul_left, pair_smul_right, hx, mul_one]; exact c.mul_inv
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [pair_smul_right, ← pair_smul_left]; exact hy
  · intro x _; simp only [smul_smul, c.mul_inv, one_smul]
  · intro y _; simp only [smul_smul, c.inv_mul, one_smul]
  · intro x _; rfl
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
