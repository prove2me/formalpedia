-- Prove2me | solution 1 for FairChores.bag_exit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:23:31.036167+00:00
-- url     : https://prove2.me/submissions/c0d3091e-cbce-4302-a852-aded673251dc

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresBagLemma
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty



set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
variable (c : Fin n → T → ℝ) (p : T → ℝ) (mu : Fin n → ℝ)
variable {c p mu}
omit [Fintype T]
namespace FairChores
theorem _root_.solution (hmu : ∀ i, 0 < mu i) {A : Finset (Fin n)} {R X Psi : Finset T}
    (hX : X ⊆ R) (hPsi : Psi ⊆ R) (hdisj : Disjoint X Psi)
    (hempty : R \ (X ∪ Psi) = ∅)
    (hP : ∀ j ∈ A, mu j ≤ cbarSum (c j) p X ∨ ∀ t ∈ Psi, mu j < cbar (c j) p t)
    (hQ : X = ∅ → ∀ t ∈ Psi, ∀ j ∈ A, 2 * mu j < cbar (c j) p t)
    (hU : ∃ j ∈ A, cbarSum (c j) p X < mu j) :
    BagGoal c p mu A R := by
  classical
  have hPsiX : Psi = R \ X := by
    ext s
    constructor
    · intro hs
      exact Finset.mem_sdiff.mpr ⟨hPsi hs, fun hsX => Finset.disjoint_left.mp hdisj hsX hs⟩
    · intro hs
      obtain ⟨hsR, hsX⟩ := Finset.mem_sdiff.mp hs
      by_contra hsPsi
      have : s ∈ R \ (X ∪ Psi) :=
        Finset.mem_sdiff.mpr ⟨hsR, fun h => (Finset.mem_union.mp h).elim hsX hsPsi⟩
      rw [hempty] at this
      exact absurd this (Finset.notMem_empty s)
  rcases Finset.eq_empty_or_nonempty X with hXe | hXne
  · left
    intro i hi t ht
    refine hQ hXe t ?_ i hi
    rw [hPsiX, hXe]
    simpa using ht
  · right
    obtain ⟨j0, hj0A, hj0⟩ := hU
    refine ⟨X, hX, hXne, j0, hj0A, ?_, ?_⟩
    · have := hmu j0
      linarith
    · intro j hjA hne
      rcases hP j hjA with h | h
      · exact Or.inl h
      · exact Or.inr fun t ht => h t (by rw [hPsiX]; exact ht)
end FairChores
