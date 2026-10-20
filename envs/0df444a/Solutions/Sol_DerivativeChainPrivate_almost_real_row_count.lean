-- Prove2me | solution 1 for DerivativeChainPrivate.almost_real_row_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:51:22.708988+00:00
-- url     : https://prove2.me/submissions/cf4216b9-a002-4791-b67e-c5c4d774f80a

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_real_coefficients_descent
import Theorems.Thm_DerivativeChainPrivate_real_root_defect_iterate
import Theorems.Thm_DerivativeChainPrivate_root_slot_nonreal_count

set_option autoImplicit false
open DerivativeChainPrivate

theorem solution {n : ℕ} (a : Fin n → ℂ) (hr : RealCoefficients a) :
    ∃ p : Polynomial ℝ, p.map Complex.ofRealHom = fromRoots a ∧
      ∀ m : ℕ, m ≤ n →
        ((Polynomial.derivative^[n - m]) p).map Complex.ofRealHom = row a m ∧
        ((Polynomial.derivative^[n - m]) p).natDegree = m ∧
        m - nonrealCount a ≤ ((Polynomial.derivative^[n - m]) p).roots.card := by
  obtain ⟨p, hp⟩ := DerivativeChainPrivate.real_coefficients_descent (fromRoots a) hr
  have hdegree : (fromRoots a).natDegree = n := by
    unfold fromRoots
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (a i))]
    simp
  have hpdegree : p.natDegree = n := by
    rwa [← hp, Polynomial.natDegree_map] at hdegree
  have hcount := DerivativeChainPrivate.root_slot_nonreal_count a p hp
  have hiter : ∀ k : ℕ, ((Polynomial.derivative^[k]) p).natDegree = n - k := by
    intro k
    induction k with
    | zero => exact hpdegree
    | succ k ih =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
      omega
  refine ⟨p, hp, ?_⟩
  intro m hm
  refine ⟨?_, ?_, ?_⟩
  · rw [← Polynomial.iterate_derivative_map, hp]
    rfl
  · rw [hiter]
    omega
  · have h := DerivativeChainPrivate.real_root_defect_iterate p (n - m)
    rw [hiter, hcount] at h
    omega
