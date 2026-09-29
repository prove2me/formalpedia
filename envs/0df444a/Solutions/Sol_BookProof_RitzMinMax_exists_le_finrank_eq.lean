-- Prove2me | solution 1 for BookProof.RitzMinMax.exists_le_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:43:43.73399+00:00
-- url     : https://prove2.me/submissions/636dd9c5-71e5-4043-8fa4-f11e35daa7cd

-- Generated from ChapterSirkRitzMinMax.lean — solution of BookProof.RitzMinMax.exists_le_finrank_eq
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax










noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {S : Submodule ℂ F} [FiniteDimensional ℂ S] {n : ℕ}
    (hn : n ≤ Module.finrank ℂ S) :
    ∃ S₀ : Submodule ℂ F, S₀ ≤ S ∧ Module.finrank ℂ S₀ = n := by

  classical
  set e := Module.finBasis ℂ S with he
  set v : Fin n → F := fun i => (e (Fin.castLE hn i) : F) with hv
  have hli : LinearIndependent ℂ v := by
    have h1 : LinearIndependent ℂ (fun i : Fin n => e (Fin.castLE hn i)) :=
      e.linearIndependent.comp _ (Fin.castLE_injective hn)
    exact h1.map' (S.subtype) (by simp [Submodule.ker_subtype])
  refine ⟨Submodule.span ℂ (Set.range v), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact (e (Fin.castLE hn i)).2
  · rw [finrank_span_eq_card hli]
    simp
