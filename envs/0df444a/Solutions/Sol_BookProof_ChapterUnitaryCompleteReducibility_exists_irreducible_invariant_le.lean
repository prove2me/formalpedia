-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:16:16.683806+00:00
-- url     : https://prove2.me/submissions/d21369e1-0cfb-42d0-bcc2-8fe1baea50f3

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_invariant_le
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} {U : Submodule ℂ V} (hU : IsInvariant ρ U) (hUne : U ≠ ⊥) :
    ∃ W ≤ U, IsIrreducibleInvariant ρ W := by

  classical
  -- Among all nonzero invariant subspaces contained in `U`, pick one of least rank.
  have hne : ∃ n : ℕ, ∃ W : Submodule ℂ V,
      W ≤ U ∧ IsInvariant ρ W ∧ W ≠ ⊥ ∧ Module.finrank ℂ W = n :=
    ⟨Module.finrank ℂ U, U, le_rfl, hU, hUne, rfl⟩
  obtain ⟨W, hWU, hWinv, hWne, hWrank⟩ := Nat.find_spec hne
  refine ⟨W, hWU, hWinv, hWne, ?_⟩
  intro Z hZW hZinv
  by_cases hZ : Z = ⊥
  · exact Or.inl hZ
  · right
    have hZU : Z ≤ U := hZW.trans hWU
    have hle : Module.finrank ℂ Z ≤ Module.finrank ℂ W := Submodule.finrank_mono hZW
    have hmin : Nat.find hne ≤ Module.finrank ℂ Z :=
      Nat.find_min' hne ⟨Z, hZU, hZinv, hZ, rfl⟩
    have : Module.finrank ℂ Z = Module.finrank ℂ W := le_antisymm hle (hWrank ▸ hmin)
    exact Submodule.eq_of_le_of_finrank_eq hZW this
