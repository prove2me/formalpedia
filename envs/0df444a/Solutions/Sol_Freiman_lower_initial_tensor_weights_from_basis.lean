-- Prove2me | solution 1 for Freiman.lower_initial_tensor_weights_from_basis
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T00:22:22.618902+00:00
-- url     : https://prove2.me/submissions/780326cd-b807-4eb1-954e-543997479dae

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem solution (x y z : ℝ)
    (hx : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (85*x)) ∧ (∑ i : Fin 3, certBernsteinBasis i (85*x))=1)
    (hy : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (3*y)) ∧ (∑ i : Fin 3, certBernsteinBasis i (3*y))=1)
    (hz : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (3*z)) ∧ (∑ i : Fin 3, certBernsteinBasis i (3*z))=1) :
    (∀ i j k : Fin 3, 0 ≤ lowerInitialWeight x y z i j k) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, lowerInitialWeight x y z i j k)=1 := by
  refine ⟨fun i j k => ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (hx.1 i) (hy.1 j)) (hz.1 k)
  · have hk : ∀ i j : Fin 3,
        (∑ k : Fin 3, lowerInitialWeight x y z i j k)
          = certBernsteinBasis i (85*x) * certBernsteinBasis j (3*y) := by
      intro i j
      simp only [lowerInitialWeight]
      rw [← Finset.mul_sum, hz.2, mul_one]
    have hj : ∀ i : Fin 3,
        (∑ j : Fin 3, ∑ k : Fin 3, lowerInitialWeight x y z i j k)
          = certBernsteinBasis i (85*x) := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ => hk i j), ← Finset.mul_sum, hy.2, mul_one]
    rw [Finset.sum_congr rfl (fun i _ => hj i), hx.2]
