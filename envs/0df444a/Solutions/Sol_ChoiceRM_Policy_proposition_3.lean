-- Prove2me | solution 1 for ChoiceRM.Policy.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:58:04.250291+00:00
-- url     : https://prove2.me/submissions/02d19bf8-d25a-431c-ac85-21e71686ba6c

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
set_option autoImplicit false
open RevenueManagement ChoiceRM.Policy

theorem solution {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k))) :
    Monotone (fun k => expRevenue P r (Sq k)) := by
  intro k l hkl
  by_contra hlt
  push_neg at hlt
  apply hnd l
  refine ⟨fun S => if S = Sq k then 1 else 0, fun S => by show (0:ℝ) ≤ (if S = Sq k then 1 else 0); split_ifs <;> norm_num, ?_, Or.inl ⟨?_, ?_⟩⟩
  · simp
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hmono hkl
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hlt
