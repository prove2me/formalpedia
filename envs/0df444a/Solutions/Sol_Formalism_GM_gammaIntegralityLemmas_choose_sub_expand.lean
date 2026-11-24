-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.choose_sub_expand
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.908137+00:00
-- url     : https://prove2.me/submissions/995bd432-5dd8-4839-9978-c13d4236cd65

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (D : ℕ) : ∀ S k : ℕ, k ≤ D → ∃ e : ℕ → ℤ, ∀ n : ℕ, S ≤ n →
    (((n - S).choose k : ℕ) : ℤ) = ∑ i ∈ range (D + 1), e i * ((n.choose i : ℕ) : ℤ) := by
  intro S
  induction S with
  | zero =>
    intro k hk
    refine ⟨fun i => if i = k then 1 else 0, fun n _ => ?_⟩
    simp only [Nat.sub_zero, ite_mul, one_mul, zero_mul]
    rw [sum_ite_eq']
    simp [show k < D + 1 by omega]
  | succ S ih =>
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun i => if i = 0 then 1 else 0, fun n _ => ?_⟩
      simp only [ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq']
      simp
    | succ k ihk =>
      intro hk
      obtain ⟨e1, he1⟩ := ih (k + 1) hk
      obtain ⟨e2, he2⟩ := ihk (by omega)
      refine ⟨fun i => e1 i - e2 i, fun n hn => ?_⟩
      have hpas : (n - S).choose (k + 1) = (n - (S + 1)).choose k + (n - (S + 1)).choose (k + 1) := by
        have : n - S = (n - (S + 1)) + 1 := by omega
        rw [this, Nat.choose_succ_succ]
      have h1 := he1 n (by omega)
      have h2 := he2 n hn
      have : (((n - (S + 1)).choose (k + 1) : ℕ) : ℤ) =
          (((n - S).choose (k + 1) : ℕ) : ℤ) - (((n - (S + 1)).choose k : ℕ) : ℤ) := by
        rw [hpas]; push_cast; ring
      rw [this, h1, h2, ← sum_sub_distrib]
      apply sum_congr rfl; intro i _; ring
end Formalism.GM.gammaIntegralityLemmas
