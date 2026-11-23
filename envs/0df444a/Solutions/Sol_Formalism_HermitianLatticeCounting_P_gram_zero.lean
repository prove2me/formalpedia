-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:47.173796+00:00
-- url     : https://prove2.me/submissions/34584518-4591-4018-854d-70ce1c921aab

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
    (hM : (Matrix.of fun a b => H.B (u a) (w b)).det = 0) :
    ∃ c : Fin n → K, c ≠ 0 ∧ ∀ b, H.B (∑ a, c a • u a) (w b) = 0 := by
  obtain ⟨c, hc, hc0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hM
  refine ⟨c, hc, fun b => ?_⟩
  rw [B_sum_left]
  exact congrFun hc0 b
end Formalism.HermitianLatticeCounting.P
