-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:21.592303+00:00
-- url     : https://prove2.me/submissions/54fae8d6-0520-4e91-a1ad-201f70dbbe5c

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Theorems.Thm_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_pick_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
namespace Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (s₀ : Finset (Submodule (NumberField.RingOfIntegers K) V))
    (h₁ : ∀ M ∈ s₀, M ∈ genus h L) (h₂ : ∀ M ∈ genus h L, ∃ N ∈ s₀, ∃ g ∈ isom h, gmap g N = M) :
    ∃ s, IsClassReps h L s := by
  classical
  have hsound : ∀ A B : Submodule (NumberField.RingOfIntegers K) V,
      (∃ g ∈ isom h, gmap g A = B) → Quotient.mk (isoSetoid h) A = Quotient.mk (isoSetoid h) B :=
    fun A B hAB => Quotient.sound hAB
  have hexact : ∀ A B : Submodule (NumberField.RingOfIntegers K) V,
      Quotient.mk (isoSetoid h) A = Quotient.mk (isoSetoid h) B → ∃ g ∈ isom h, gmap g A = B :=
    fun A B e => Quotient.exact e
  refine ⟨s₀.image (fun N => pick h s₀ (Quotient.mk (isoSetoid h) N)), ?_, ?_⟩
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
    exact h₁ _ (pick_spec h s₀ hN).1
  · intro M hM
    obtain ⟨N, hN, g, hg, e⟩ := h₂ M hM
    obtain ⟨g', hg', e'⟩ := hexact _ _ (pick_spec h s₀ hN).2
    have hE : gmap (g * g') (pick h s₀ (Quotient.mk (isoSetoid h) N)) = M := by
      rw [gmap_mul, e', e]
    refine ⟨pick h s₀ (Quotient.mk (isoSetoid h) N),
      ⟨Finset.mem_image.mpr ⟨N, hN, rfl⟩, g * g', (isom h).mul_mem hg hg', hE⟩, ?_⟩
    rintro P ⟨hP, g₁, hg₁, e₁⟩
    obtain ⟨N₁, hN₁, rfl⟩ := Finset.mem_image.mp hP
    have hrel : Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) N₁)) =
        Quotient.mk (isoSetoid h) (pick h s₀ (Quotient.mk (isoSetoid h) N)) := by
      apply hsound
      refine ⟨(g * g')⁻¹ * g₁,
        (isom h).mul_mem ((isom h).inv_mem ((isom h).mul_mem hg hg')) hg₁, ?_⟩
      rw [gmap_mul, e₁, ← hE, gmap_inv_gmap]
    have hN : Quotient.mk (isoSetoid h) N₁ = Quotient.mk (isoSetoid h) N :=
      (pick_spec h s₀ hN₁).2.symm.trans (hrel.trans (pick_spec h s₀ hN).2)
    rw [hN]
end Formalism.ThetaLiftIndependence.DefiniteClassRepresentatives
