-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.fs_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:41.763793+00:00
-- url     : https://prove2.me/submissions/c7dfc80a-93a2-4c5e-9fd0-7ecf7b4d5cf9

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_fs_exp

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
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (A x : ℝ) (hA0 : 0 ≤ A) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k r f : ℕ) (hk : r + 2 ≤ k) :
    0 ≤ ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ∧
    ∑ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ≤ r * (A * x ^ ((k - 2) * f)) := by
  refine ⟨Finset.sum_nonneg (fun j _ => by positivity), ?_⟩
  have hterm : ∀ j ∈ Finset.Icc 1 r, A * x ^ (j * (k - 1 - j) * f) ≤ A * x ^ ((k - 2) * f) := by
    intro j hj
    obtain ⟨hj1, hjr⟩ := Finset.mem_Icc.1 hj
    apply mul_le_mul_of_nonneg_left _ hA0
    exact pow_le_pow_of_le_one hx0 hx1 (fs_exp j k f hj1 (by omega))
  have := Finset.sum_le_card_nsmul (Finset.Icc 1 r) (fun j => A * x ^ (j * (k - 1 - j) * f)) _ hterm
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at this
  exact this
end Formalism.HermitianLatticeCounting.P
