-- Prove2me | solution 1 for FlexibleNRM.vfa_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:26:15.636197+00:00
-- url     : https://prove2.me/submissions/1026b5c8-3c48-43e2-9257-86c223165cce

import Mathlib
import Definitions.Def_FlexibleNRM_vfa

open FlexibleNRM in
theorem solution {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ) (t : ℕ) :
    vfa N γ t 0 = ∑ j, ∑ p ∈ N.R j, γ j p t := by
  have hval : ∀ w : Fin m → ℕ, (∀ i, w i = N.c i) →
      vfaResource N γ t (fun i => (w i : ℤ)) = ∑ j, ∑ p ∈ N.R j, γ j p t := by
    intro w hw
    unfold vfaResource
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
    have h1 : ∀ i, (((w i : ℤ)) : ℝ) / (N.c i : ℝ) = 1 := by
      intro i
      rw [hw i]
      have : (N.c i : ℝ) ≠ 0 := by exact_mod_cast (N.c_pos i).ne'
      push_cast
      exact div_self this
    have hpsi : psi N p (fun i => (w i : ℤ)) = 1 := by
      unfold psi
      obtain ⟨i0, hi0⟩ := N.A_nonempty p
      apply le_antisymm
      · exact (Finset.inf'_le _ hi0).trans (le_of_eq (h1 i0))
      · exact Finset.le_inf' _ _ fun i _ => le_of_eq (h1 i).symm
    rw [hpsi, mul_one]
  have hset : {v : ℝ | ∃ (y : Fin n → Fin r → ℕ) (w : Fin m → ℕ),
      (∀ j, ∑ p ∈ N.R j, y j p = (0 : Fin n → ℕ) j) ∧
      (∀ i, ∑ j, ∑ p ∈ N.R j, N.a i p * y j p + w i = N.c i) ∧
      v = vfaResource N γ t (fun i => (w i : ℤ))} = {∑ j, ∑ p ∈ N.R j, γ j p t} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, w, hy, hw, rfl⟩
      have hy0 : ∀ j, ∀ p ∈ N.R j, y j p = 0 := fun j p hp =>
        (Finset.sum_eq_zero_iff.mp (hy j)) p hp
      have hw' : ∀ i, w i = N.c i := by
        intro i
        have := hw i
        rw [Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero fun p hp => by
          rw [hy0 j p hp, mul_zero])] at this
        omega
      exact hval w hw'
    · rintro rfl
      refine ⟨fun _ _ => 0, fun i => N.c i, fun j => by simp, fun i => by simp, ?_⟩
      exact (hval _ fun i => rfl).symm
  unfold vfa
  rw [hset, csSup_singleton]
