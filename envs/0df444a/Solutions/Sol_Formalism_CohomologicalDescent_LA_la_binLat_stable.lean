-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_binLat_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:52.260714+00:00
-- url     : https://prove2.me/submissions/3b0ddf20-65ed-47ca-963f-7f072a633c39

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mem_of_dvd
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_xy_zero
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_xy_one
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_rowDiv_nat
import Theorems.Thm_Formalism_CohomologicalDescent_LA_choose_dvd_choose_mul_right
import Theorems.Thm_Formalism_CohomologicalDescent_LA_choose_dvd_choose_mul_left
import Theorems.Thm_Formalism_CohomologicalDescent_LA_fin_two_eq_zero_or_one
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (R : Type) [CommRing R] {n : ℕ} (s : Fin n) (d : ℕ) (a b : Fin 2) (k : ℕ)
    (f : MvPolynomial (Fin 2 × Fin n) R) (hf : f ∈ la_binLat R s d) :
    rowDiv R a b k f ∈ la_binLat R s d := by
  rw [la_binLat] at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    rw [la_rowDiv_nat]
    rcases fin_two_eq_zero_or_one b with rfl | rfl <;> rcases fin_two_eq_zero_or_one a with rfl | rfl
    · rw [la_rowDiv_xy_zero]
      by_cases hk : k ≤ p
      · have e : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * (((p.choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((0 : Fin 2), s) ^ (p - k) * X ((0 : Fin 2), s) ^ k * X ((1 : Fin 2), s) ^ q)) =
            (p.choose k : R) • (((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q) := by
          rw [← pow_add, Nat.sub_add_cancel hk, MvPolynomial.smul_eq_C_mul, map_natCast, la_xy]
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, q, hpq, rfl⟩)
      · rw [Nat.choose_eq_zero_of_lt (show p < k by omega)]
        simp
    · rw [la_rowDiv_xy_zero]
      by_cases hk : k ≤ p
      · obtain ⟨p', rfl⟩ : ∃ p', p = p' + k := ⟨p - k, by omega⟩
        have e : ((p' + k + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * ((((p' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((0 : Fin 2), s) ^ (p' + k - k) * X ((1 : Fin 2), s) ^ k * X ((1 : Fin 2), s) ^ q)) =
            (((p' + k + q).choose q * (p' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
              la_xy R s p' (k + q) := by
          rw [Nat.add_sub_cancel, la_xy]
          push_cast
          ring
        rw [e]
        exact la_mem_of_dvd R s (by omega) (choose_dvd_choose_mul_right p' k q)
      · rw [Nat.choose_eq_zero_of_lt (show p < k by omega)]
        simp
    · rw [la_rowDiv_xy_one]
      by_cases hk : k ≤ q
      · obtain ⟨q', rfl⟩ : ∃ q', q = q' + k := ⟨q - k, by omega⟩
        have e : ((p + (q' + k)).choose (q' + k) : MvPolynomial (Fin 2 × Fin n) R) *
            ((((q' + k).choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((1 : Fin 2), s) ^ (q' + k - k) * X ((0 : Fin 2), s) ^ k * X ((0 : Fin 2), s) ^ p)) =
            (((p + (q' + k)).choose (q' + k) * (q' + k).choose k : ℕ) :
              MvPolynomial (Fin 2 × Fin n) R) * la_xy R s (p + k) q' := by
          rw [Nat.add_sub_cancel, la_xy]
          push_cast
          ring
        rw [e]
        exact la_mem_of_dvd R s (by omega) (choose_dvd_choose_mul_left p k q')
      · rw [Nat.choose_eq_zero_of_lt (show q < k by omega)]
        simp
    · rw [la_rowDiv_xy_one]
      by_cases hk : k ≤ q
      · have e : ((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * (((q.choose k : ℕ) : MvPolynomial (Fin 2 × Fin n) R) *
            (X ((1 : Fin 2), s) ^ (q - k) * X ((1 : Fin 2), s) ^ k * X ((0 : Fin 2), s) ^ p)) =
            (q.choose k : R) • (((p + q).choose q : MvPolynomial (Fin 2 × Fin n) R) * la_xy R s p q) := by
          rw [← pow_add, Nat.sub_add_cancel hk, MvPolynomial.smul_eq_C_mul, map_natCast, la_xy]
          ring
        rw [e]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, q, hpq, rfl⟩)
      · rw [Nat.choose_eq_zero_of_lt (show q < k by omega)]
        simp
  | zero =>
    rw [show rowDiv R a b k 0 = 0 from by simp [rowDiv]]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [show rowDiv R a b k (x + y) = rowDiv R a b k x + rowDiv R a b k y from by simp [rowDiv]]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [show rowDiv R a b k (c • x) = c • rowDiv R a b k x from by simp [rowDiv]]
    exact Submodule.smul_mem _ c hx
end Formalism.CohomologicalDescent.LA
