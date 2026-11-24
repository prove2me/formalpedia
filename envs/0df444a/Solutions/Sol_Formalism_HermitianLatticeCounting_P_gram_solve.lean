-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_solve
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:55.001737+00:00
-- url     : https://prove2.me/submissions/d0a0c64a-fbfb-4cc3-b410-13cd7bbdeaa9

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_sum_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (H : HermSpace K V) {n : ℕ} (u w : Fin n → V)
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det ≠ 0) (t : Fin n → K) :
    ∃ c : Fin n → K, ∀ b, H.B (∑ a, c a • u a) (w b) = t b := by
  have hu : IsUnit (Matrix.of fun a b => H.B (u a) (w b)).det := isUnit_iff_ne_zero.2 hM
  refine ⟨Matrix.vecMul t (Matrix.of fun a b => H.B (u a) (w b))⁻¹, fun b => ?_⟩
  rw [B_sum_left]
  have h1 : Matrix.vecMul (Matrix.vecMul t (Matrix.of fun a b => H.B (u a) (w b))⁻¹) (Matrix.of fun a b => H.B (u a) (w b)) = t := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  rw [← congrFun h1 b]
  rfl
end Formalism.HermitianLatticeCounting.P
