-- Prove2me | solution 1 for Formalism.CountingSumsFrames.pow_log_div_choose_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:28.911698+00:00
-- url     : https://prove2.me/submissions/10a48437-d19d-4069-b5ac-e4f8bf74f658

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
namespace Formalism.CountingSumsFrames
theorem _root_.solution {K : Type} [Field K] [CharZero K] (R : Subring K) (p : ℕ) (hp : p.Prime) (hR : PLocal R p)
    (n N l : ℕ) (hn : n ≤ N) : (p : K) ^ Nat.log p N / ((n.choose l : ℕ) : K) ∈ R := by
  by_cases hc : n.choose l = 0
  · rw [hc]; simp
  · obtain ⟨e, u, hu, hcu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc p hp.ne_one
    have he : e ≤ Nat.log p N := by
      have h1 : p ^ e ∣ n.choose l := ⟨u, hcu⟩
      have h2 : e ≤ (n.choose l).factorization p := (hp.pow_dvd_iff_le_factorization hc).1 h1
      exact h2.trans (Nat.factorization_choose_le_log.trans (Nat.log_mono_right hn))
    have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hu0 : (u : K) ≠ 0 := by
      refine Nat.cast_ne_zero.2 ?_
      rintro rfl
      exact hu (dvd_zero p)
    have : (p : K) ^ Nat.log p N / ((n.choose l : ℕ) : K) = (p : K) ^ (Nat.log p N - e) * (u : K)⁻¹ := by
      rw [hcu]
      push_cast
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le he
      rw [hd, Nat.add_sub_cancel_left, pow_add]
      field_simp
    rw [this]
    exact R.mul_mem (R.pow_mem (natCast_mem R p) _) (hR u hu)
end Formalism.CountingSumsFrames
