-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.unique_solution_card_le
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:55:48.963948+00:00
-- url     : https://prove2.me/submissions/4c90b1f5-bf63-46c3-a688-a33cd5e7228b

import Mathlib

theorem solution {K : Type*} [Field K] {r m : ℕ} (A : Matrix (Fin r) (Fin m) K)
    (b : Fin r → K) (y₀ : Fin m → K) (hy₀ : A.mulVec y₀ = b)
    (huniq : ∀ y, A.mulVec y = b → y = y₀) : m ≤ r := by
  by_contra hlt
  push_neg at hlt
  have hker : LinearMap.ker (Matrix.mulVecLin A) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hlt)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hAv : A.mulVec v = 0 := by
    have := LinearMap.mem_ker.1 hv
    simpa using this
  have h := huniq (y₀ + v) (by rw [Matrix.mulVec_add, hy₀, hAv, add_zero])
  apply hv0
  simpa using h
