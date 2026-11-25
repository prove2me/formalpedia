-- Prove2me | solution 1 for Formalism.HN.piSum_single_mu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:52.780434+00:00
-- url     : https://prove2.me/submissions/0d5bb069-6aa4-449e-92f0-1b78b747fab1

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
import Theorems.Thm_Formalism_HN_piSum_single
import Theorems.Thm_Formalism_HN_hnSum_isLat_mono
import Theorems.Thm_Formalism_HN_slope_characterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
variable [∀ i, FiniteDimensional ℝ (E i)]
private theorem linearMap_single_injective (i : ι) : Function.Injective (LinearMap.single R V i) := by
  intro a b h
  have h' := congrFun h i
  simpa using h'
private theorem exists_eq_map_single_of_le_map_single {i : ι} {P : Submodule R (V i)} {N : Submodule R (∀ i, V i)}
    (h : N ≤ P.map (LinearMap.single R V i)) :
    ∃ N' : Submodule R (V i), N' ≤ P ∧ N = N'.map (LinearMap.single R V i) := by
  refine ⟨N.comap (LinearMap.single R V i), ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (h (Submodule.mem_comap.1 hx))
    exact (linearMap_single_injective (R := R) (V := V) i hyx) ▸ hy
  · apply le_antisymm
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Submodule.mem_map.1 (h hx)
      exact Submodule.mem_map_of_mem (Submodule.mem_comap.2 hx)
    · exact Submodule.map_comap_le _ _
end
section
variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
end
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
end
end Formalism.HN
namespace Formalism.HN
universe uR uι uV uE uS
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (ρ : ∀ i, V i →+ E i)
variable [∀ i, FiniteDimensional ℝ (E i)]
namespace Formalism.HN
theorem _root_.solution (L : ∀ i, Submodule R (V i)) (i : ι) (hL : IsLat (ρ i) (L i))
    (hL0 : L i ≠ ⊥) :
    piSumS L i ≠ ⊥ ∧ ∀ θ : ℝ,
      (muMax (piReal ρ) (piSumS L i) ≤ θ ↔ muMax (ρ i) (L i) ≤ θ) ∧
      (θ ≤ muMin (piReal ρ) (piSumS L i) ↔ θ ≤ muMin (ρ i) (L i)) := by
  have hcomp : IsLat (piReal ρ) (piSumS L i) ∧
      rk (piReal ρ) (piSumS L i) = rk (ρ i) (L i) ∧
      deg (piReal ρ) (piSumS L i) = deg (ρ i) (L i) :=
    piSum_single ρ i (L i) hL
  have hc0 : piSumS L i ≠ ⊥ := by
    intro h
    apply hL0
    apply Submodule.map_injective_of_injective (linearMap_single_injective (R := R) (V := V) i)
    rw [Submodule.map_bot]
    exact h
  have hsub : ∀ N : Submodule R (V i), N ≤ L i → IsLat (ρ i) N :=
    fun N hN => hnSum_isLat_mono (ρ i) hL hN
  refine ⟨hc0, fun θ => ?_⟩
  have EP := slope_characterization R (∀ i, V i) (PiLp 2 E) (piReal ρ) (piSumS L i)
    hcomp.1 hc0
  have EL := slope_characterization R (V i) (E i) (ρ i) (L i) hL hL0
  rw [EP.1 θ, EL.1 θ, EP.2.1 θ, EL.2.1 θ]
  refine ⟨⟨fun H N hN => ?_, fun H N hN => ?_⟩, ⟨fun H N hN => ?_, fun H N hN => ?_⟩⟩
  · have h := H (N.map (LinearMap.single R V i)) (Submodule.map_mono hN)
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N (hsub N hN)
    rw [hr, hd] at h
    exact h
  · obtain ⟨N', hN', rfl⟩ := exists_eq_map_single_of_le_map_single (i := i) (P := L i) hN
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N' (hsub N' hN')
    rw [hr, hd]
    exact H N' hN'
  · have h := H (N.map (LinearMap.single R V i)) (Submodule.map_mono hN)
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N (hsub N hN)
    rw [hcomp.2.1, hcomp.2.2, hr, hd] at h
    exact h
  · obtain ⟨N', hN', rfl⟩ := exists_eq_map_single_of_le_map_single (i := i) (P := L i) hN
    obtain ⟨-, hr, hd⟩ := piSum_single ρ i N' (hsub N' hN')
    rw [hcomp.2.1, hcomp.2.2, hr, hd]
    exact H N' hN'
end Formalism.HN
