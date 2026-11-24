-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.minkowski_divisor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:46.479212+00:00
-- url     : https://prove2.me/submissions/d251e0e7-b29c-4448-bd17-a71f01467916

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MinkowskiDivisorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.TraceIntegrality
open Finset
private theorem mink_term (n p i : ℕ) (hp : 2 ≤ p) :
    n / (p ^ i * (p - 1)) ≤ 2 * n / p ^ (1 + i) := by
  have hpos : 0 < p ^ (1 + i) := Nat.pow_pos (by omega)
  rw [Nat.le_div_iff_mul_le hpos]
  have h1 : n / (p ^ i * (p - 1)) * (p ^ i * (p - 1)) ≤ n := Nat.div_mul_le_self _ _
  have h2 : p ≤ 2 * (p - 1) := by omega
  calc n / (p ^ i * (p - 1)) * p ^ (1 + i)
      = n / (p ^ i * (p - 1)) * p ^ i * p := by rw [pow_add, pow_one]; ring
    _ ≤ n / (p ^ i * (p - 1)) * p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h2
    _ = 2 * (n / (p ^ i * (p - 1)) * (p ^ i * (p - 1))) := by ring
    _ ≤ 2 * n := Nat.mul_le_mul_left _ h1
end Formalism.HermitianLattices.TraceIntegrality
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : Minkowski_div := by
  intro n p hp
  have : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (2 * n) < 2 * n + 2 :=
    lt_of_le_of_lt (Nat.log_le_self _ _) (by omega)
  rw [padicValNat_factorial hlog]
  calc ∑ i ∈ range (n + 1), n / (p ^ i * (p - 1))
      ≤ ∑ i ∈ range (n + 1), 2 * n / p ^ (1 + i) :=
        Finset.sum_le_sum (fun i _ => mink_term n p i hp.two_le)
    _ = ∑ i ∈ Ico 1 (n + 2), 2 * n / p ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]; rfl
    _ ≤ ∑ i ∈ Ico 1 (2 * n + 2), 2 * n / p ^ i := by
        apply Finset.sum_le_sum_of_subset
        apply Finset.Ico_subset_Ico le_rfl
        omega
end Formalism.HermitianLattices.TraceIntegrality
