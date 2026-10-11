-- Prove2me | solution 1 for BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:16:31.397711+00:00
-- url     : https://prove2.me/submissions/4cee001c-f4d9-4c51-8cef-e240089184bb

-- Generated from ChapterUnitaryCompleteReducibility.lean — solution of BookProof.ChapterUnitaryCompleteReducibility.exists_irreducible_decomposition
import Mathlib
import Definitions.Def_ChapterUnitaryCompleteReducibility
import Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_orthogonal_isInvariant
import Theorems.Thm_BookProof_ChapterUnitaryCompleteReducibility_exists_irreducible_invariant_le
import Definitions.Def_ChapterMaschkeFiniteGroup
open BookProof.ChapterUnitaryCompleteReducibility




open Submodule

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

variable {G : Type*} [Group G] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

set_option maxHeartbeats 1000000 in
theorem solution [FiniteDimensional ℂ V]
    {ρ : G →* (V ≃ₗᵢ[ℂ] V)} (U : Submodule ℂ V) (hU : IsInvariant ρ U) :
    ∃ L : List (Submodule ℂ V),
      (∀ W ∈ L, W ≤ U ∧ IsIrreducibleInvariant ρ W) ∧
        L.foldr (· ⊔ ·) ⊥ = U := by

  classical
  induction hn : Module.finrank ℂ U using Nat.strong_induction_on generalizing U with
  | _ n ih =>
    by_cases hUbot : U = ⊥
    · exact ⟨[], by simp, by simp [hUbot]⟩
    obtain ⟨W, hWU, hWirr⟩ := exists_irreducible_invariant_le hU hUbot
    have hWinv : IsInvariant ρ W := hWirr.1
    have hWne : W ≠ ⊥ := hWirr.2.1
    have hcompl : IsCompl W Wᗮ :=
      Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
    set U' : Submodule ℂ V := U ⊓ Wᗮ with hU'def
    have hU'inv : IsInvariant ρ U' := by
      intro g x hx
      exact ⟨hU g x hx.1, orthogonal_isInvariant hWinv g x hx.2⟩
    have hsup : W ⊔ U' = U := by
      apply le_antisymm
      · exact sup_le hWU inf_le_left
      · intro u hu
        have hmem : u ∈ W ⊔ Wᗮ := by rw [hcompl.sup_eq_top]; trivial
        obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hmem
        have hwU : w ∈ U := hWU hw
        have hzU : z ∈ U := by
          have hz' : z = (w + z) - w := by abel
          rw [hz']
          exact U.sub_mem hu hwU
        exact Submodule.mem_sup.2 ⟨w, hw, z, ⟨hzU, hz⟩, rfl⟩
    have hdisj : W ⊓ U' = ⊥ := by
      have hle : W ⊓ U' ≤ W ⊓ Wᗮ := inf_le_inf_left W inf_le_right
      rw [hcompl.inf_eq_bot] at hle
      exact le_bot_iff.1 hle
    have hWpos : 0 < Module.finrank ℂ W :=
      Module.finrank_pos_iff.2 (Submodule.nontrivial_iff_ne_bot.2 hWne)
    have hrank : Module.finrank ℂ W + Module.finrank ℂ U' = Module.finrank ℂ U := by
      have := Submodule.finrank_sup_add_finrank_inf_eq W U'
      rw [hsup, hdisj] at this
      simpa using this.symm
    have hlt : Module.finrank ℂ U' < n := by omega
    obtain ⟨L, hL, hLsup⟩ := ih _ hlt U' hU'inv rfl
    refine ⟨W :: L, ?_, ?_⟩
    · intro Z hZ
      rcases List.mem_cons.1 hZ with rfl | hZL
      · exact ⟨hWU, hWirr⟩
      · exact ⟨(hL Z hZL).1.trans inf_le_left, (hL Z hZL).2⟩
    · simp [hLsup, hsup]
