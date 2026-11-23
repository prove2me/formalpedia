-- Prove2me | solution 1 for Formalism.HC.Der.Rd.adjoin_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:19.149071+00:00
-- url     : https://prove2.me/submissions/521934e3-be5b-4d5d-b6b2-4ad2e3978d32

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial ArithmeticFunction
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [NumberField L] [IsCyclotomicExtension {N} ℚ L] {ζ : L}
  (hζ : IsPrimitiveRoot ζ N) (E : Type*) [Field E] [NumberField E] [Algebra E L]
include hζ
set_option maxHeartbeats 800000
namespace Formalism.HC.Der.Rd
theorem _root_.solution : Algebra.adjoin E {ζ} = ⊤ := by
  have h1 : Algebra.adjoin ℚ ({ζ} : Set L) = ⊤ := IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  refine eq_top_iff.2 fun x hxt => ?_
  clear hxt
  have hx : x ∈ Algebra.adjoin ℚ ({ζ} : Set L) := by rw [h1]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    rw [eq_ratCast (algebraMap ℚ L) r, ← map_ratCast (algebraMap E L) r]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end Formalism.HC.Der.Rd
