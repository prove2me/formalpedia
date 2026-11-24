-- Prove2me | solution 1 for Formalism.HN.lattice_rerealization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:19.449772+00:00
-- url     : https://prove2.me/submissions/412bb9db-10c9-4ad9-89cd-f75d5ab650a8

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Theorems.Thm_Formalism_HN_Rerealization_transfer
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_norm_sq_realize
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_satR_mem_zl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
open Rerealization
namespace Formalism.HN
theorem _root_.solution : Rerealize := by
  intro K V ι V'' κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b'' X'' ψ hX hX'' hψ hnorm A hA
  have hψ' : Function.Injective (ψ.restrictScalars (𝓞 K)) := hψ
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : V →+ EuclideanSpace ℝ (InfinitePlace K × κ × Fin 2),
      ρ₂ = (Formalism.HermitianLatticesTheory.realize b'' X'').comp ψ.toAddMonoidHom := ⟨_, rfl⟩
  have hρ₂x : ∀ x, ρ₂ x = Formalism.HermitianLatticesTheory.realize b'' X'' (ψ x) := fun x => by rw [hρ₂]; rfl
  have hn : ∀ x, ‖ρ₂ x‖ = ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have h2 : ‖ρ₂ x‖ ^ 2 = ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 := by
      rw [hρ₂x, PlaceOperatorNorms.norm_sq_realize, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm]
    have h3 := congrArg Real.sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3
  have hzl : ∀ N : Submodule (𝓞 K) V,
      zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) = zl ρ₂ N := by
    intro N
    ext y
    rw [satR_mem_zl, satR_mem_zl]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hρ₂x x⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨ψ x, ⟨x, hx, rfl⟩, (hρ₂x x).symm⟩
  have hmc : ∀ N'' : Submodule (𝓞 K) V'', N'' ≤ A.map (ψ.restrictScalars (𝓞 K)) →
      ∃ N : Submodule (𝓞 K) V, N ≤ A ∧ N.map (ψ.restrictScalars (𝓞 K)) = N'' := by
    intro N'' h
    refine ⟨N''.comap (ψ.restrictScalars (𝓞 K)), ?_, ?_⟩
    · intro x hx
      obtain ⟨x', hx', hxx'⟩ := h hx
      rw [← hψ' hxx']
      exact hx'
    · apply le_antisymm (Submodule.map_comap_le _ _)
      intro y hy
      obtain ⟨x, -, rfl⟩ := h hy
      exact ⟨x, hy, rfl⟩
  have hle : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) ≤ A.map (ψ.restrictScalars (𝓞 K)) ↔ N ≤ A :=
    fun N => Submodule.map_le_map_iff_of_injective hψ' N A
  have hbot : ∀ N : Submodule (𝓞 K) V, N.map (ψ.restrictScalars (𝓞 K)) = ⊥ ↔ N = ⊥ := by
    intro N
    rw [← Submodule.map_bot (ψ.restrictScalars (𝓞 K))]
    exact (Submodule.map_injective_of_injective hψ').eq_iff
  have hneA : ∀ N : Submodule (𝓞 K) V,
      N.map (ψ.restrictScalars (𝓞 K)) = A.map (ψ.restrictScalars (𝓞 K)) ↔ N = A :=
    fun N => (Submodule.map_injective_of_injective hψ').eq_iff
  have hrkK : ∀ N : Submodule (𝓞 K) V, rkK (N.map (ψ.restrictScalars (𝓞 K))) = rkK N := by
    intro N
    unfold rkK
    have hs : Submodule.span K ((N.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V'') : Set V'') =
        (Submodule.span K (N : Set V)).map ψ := by
      rw [Submodule.map_coe, ← Submodule.span_image]
      rfl
    rw [hs]
    exact (Submodule.equivMapOfInjective ψ hψ _).finrank_eq.symm
  have hlatA : IsLat (Formalism.HermitianLatticesTheory.realize b X) A := (place_lattice_structure K V ι b X hX A hA).1
  have hlatA'' : IsLat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))) :=
    (place_lattice_structure K V'' κ b'' X'' hX'' _ (hA.map _)).1
  have hlatA₂ : IsLat ρ₂ A := by
    refine ⟨?_, ?_⟩
    · intro x hx y hy h
      rw [hρ₂x, hρ₂x] at h
      exact hψ (hlatA''.1 (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) h)
    · rw [← hzl]
      exact hlatA''.2
  obtain ⟨T1, T2, T3⟩ := transfer (Formalism.HermitianLatticesTheory.realize b X) ρ₂ hn A hlatA hlatA₂
  have hht : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      ht b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = ht b X N := by
    intro N hN
    unfold ht
    rw [hrkK, hzl, (T1 N hN).1]
  have hsize : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      size b'' X'' (N.map (ψ.restrictScalars (𝓞 K))) = size b X N := by
    intro N hN
    unfold size
    rw [hht N hN, hrkK]
  have hslope : ∀ N : Submodule (𝓞 K) V, N ≤ A →
      slope (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))) =
        slope (Formalism.HermitianLatticesTheory.realize b X) N := by
    intro N hN
    rw [← (T1 N hN).2.2.2]
    unfold slope
    rw [hzl]
  have hsat : ∀ N : Submodule (𝓞 K) V,
      IsSat (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K)))
        (N.map (ψ.restrictScalars (𝓞 K))) ↔ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N := by
    intro N
    rw [← T2 N]
    unfold IsSat
    rw [hzl, hzl, hle]
  have hqs : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (A.map (ψ.restrictScalars (𝓞 K))))
        (zl (Formalism.HermitianLatticesTheory.realize b'' X'') (N.map (ψ.restrictScalars (𝓞 K))))) =
      Formalism.F.slope (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) A) (zl (Formalism.HermitianLatticesTheory.realize b X) N)) := by
    intro N hN
    rw [hzl, hzl]
    exact (T3 N hN).2
  have hsizeQ : ∀ N : Submodule (𝓞 K) V, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N →
      sizeQ b'' X'' (A.map (ψ.restrictScalars (𝓞 K))) (N.map (ψ.restrictScalars (𝓞 K))) =
        sizeQ b X A N := by
    intro N hN
    unfold sizeQ htQ
    rw [hrkK, hrkK, hzl, hzl, (T3 N hN).1]
  refine ⟨hht A le_rfl, hsize A le_rfl, hslope A le_rfl, ?_, ?_, ?_, ?_⟩
  · unfold muMax
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hslope N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hslope N hN⟩
  · unfold muMin
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hqs N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hqs N hs⟩
  · unfold leastSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hN'', hne, rfl⟩
      obtain ⟨N, hN, rfl⟩ := hmc N'' hN''
      exact ⟨N, hN, fun h => hne ((hbot N).2 h), (hsize N hN).symm⟩
    · rintro ⟨N, hN, hne, rfl⟩
      exact ⟨_, (hle N).2 hN, fun h => hne ((hbot N).1 h), hsize N hN⟩
  · unfold largestSize
    congr 1
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨N'', hs, hne, rfl⟩
      obtain ⟨N, -, rfl⟩ := hmc N'' hs.1
      have hs' := (hsat N).1 hs
      exact ⟨N, hs', fun h => hne ((hneA N).2 h), (hsizeQ N hs').symm⟩
    · rintro ⟨N, hs, hne, rfl⟩
      exact ⟨_, (hsat N).2 hs, fun h => hne ((hneA N).1 h), hsizeQ N hs⟩
end Formalism.HN
