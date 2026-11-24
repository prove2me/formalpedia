-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_sq_orthogonal_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:45.819797+00:00
-- url     : https://prove2.me/submissions/a4ce368b-4ae5-4f92-8669-704cb36e6853

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {j : ℕ} (h : Fin j → U) (horth : ∀ k l, k ≠ l → inner ℂ (h k) (h l) = 0)
    (h1 : ∀ k, ‖h k‖ ≤ 1) (c : Fin j → ℂ) : ‖∑ k, c k • h k‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 := by
  have e : inner ℂ (∑ k, c k • h k) (∑ k, c k • h k) = ((∑ k, ‖c k • h k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [sum_inner, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [inner_self_eq_norm_sq_to_K]; rfl
    · intro l _ hl
      rw [inner_smul_left, inner_smul_right, horth l k hl]; simp
    · simp
  have e2 : ‖∑ k, c k • h k‖ ^ 2 = ∑ k, ‖c k • h k‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (∑ k, c k • h k)
    rw [e] at this
    rw [← this]; exact (Complex.ofReal_re _).symm
  rw [e2]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_smul, mul_pow]
  have : ‖h k‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (h1 k)
  nlinarith [sq_nonneg ‖c k‖]
end Formalism.HermitianLatticeCounting.P
