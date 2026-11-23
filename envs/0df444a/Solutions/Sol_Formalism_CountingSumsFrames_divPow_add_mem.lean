-- Prove2me | solution 1 for Formalism.CountingSumsFrames.divPow_add_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:30.599853+00:00
-- url     : https://prove2.me/submissions/a95c17de-6bf0-4aaf-8b4f-74604d6b222b

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
variable {K E : Type*} [Field K] [CharZero K] [Ring E] [Algebra K E]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (S : Subsemiring E) (a b : E) (hab : Commute a b)
    (ha : ∀ n : ℕ, ((n.factorial : K)⁻¹) • a ^ n ∈ S) (hb : ∀ n : ℕ, ((n.factorial : K)⁻¹) • b ^ n ∈ S)
    (n : ℕ) : ((n.factorial : K)⁻¹) • (a + b) ^ n ∈ S := by
  rw [hab.add_pow', Finset.smul_sum]
  refine S.sum_mem ?_
  rintro ⟨i, j⟩ hij
  have hn : i + j = n := by simpa using hij
  subst hn
  have key : (((i + j).factorial : K)⁻¹) • ((i + j).choose i • (a ^ i * b ^ j)) =
      (((i.factorial : K)⁻¹) • a ^ i) * (((j.factorial : K)⁻¹) • b ^ j) := by
    rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul K, smul_smul]
    congr 1
    have h1 : (((i + j).choose i * i.factorial * j.factorial : ℕ) : K) = ((i + j).factorial : K) := by
      rw [Nat.choose_symm_add, Nat.add_choose_mul_factorial_mul_factorial]
    have hi : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
    have hij' : ((i + j).factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    push_cast at h1
    field_simp
    linear_combination h1
  simp only
  rw [key]
  exact S.mul_mem (ha i) (hb j)
end Formalism.CountingSumsFrames
