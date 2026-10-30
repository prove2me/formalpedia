-- Prove2me | solution 1 for DerivativeChainContinuation.positive_actual_row_class
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:55:32.152788+00:00
-- url     : https://prove2.me/submissions/92459976-cd81-4ac0-b414-6810ce8c48f9

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveSpokeClosure
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_positive_spoke_all_ordinary_rows
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators

theorem actual_complex_source_natDegree {n : ℕ} (a : Fin (n+1) → ℂ) :
    (fromRoots a).natDegree=n+1 := by
  simp only [fromRoots]
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C (a i))]
  simp
























end DerivativeChainContinuation

theorem solution {n : ℕ} (a : Fin (n+1) → ℂ)
    (k r : ℕ) (Q : Polynomial ℝ) (hk : 2 ≤ k) (hQ : PositiveQuotient Q)
    (hp : fromRoots a=spokePoly k r Q) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n+1) :
    ∃ s : ℕ, ∃ V : Polynomial ℝ, PositiveQuotient V ∧ row a m=spokePoly k s V := by
  have hd : (spokePoly k r Q).natDegree=n+1 := by rw [←hp,actual_complex_source_natDegree]
  obtain ⟨s,V,hV,heq⟩ := positive_spoke_all_ordinary_rows n k r Q hk hQ hd (n+1-m) (by omega)
  exact ⟨s,V,hV,by simpa only [row,hp] using heq⟩
