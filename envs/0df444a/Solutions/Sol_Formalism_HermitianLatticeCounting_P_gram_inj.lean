-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:54.071557+00:00
-- url     : https://prove2.me/submissions/55d3576e-0909-415f-a496-ca566a79fb9d

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
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det ≠ 0) (c : Fin n → K)
    (h : ∀ b, H.B (∑ a, c a • u a) (w b) = 0) : c = 0 := by
  have hu : IsUnit (Matrix.of fun a b => H.B (u a) (w b)).det := isUnit_iff_ne_zero.2 hM
  have h1 : Matrix.vecMul c (Matrix.of fun a b => H.B (u a) (w b)) = 0 := by
    funext b
    show _ = (0 : K)
    rw [← h b, B_sum_left]
    rfl
  have h2 := congrArg (fun y => Matrix.vecMul y (Matrix.of fun a b => H.B (u a) (w b))⁻¹) h1
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using h2
end Formalism.HermitianLatticeCounting.P
