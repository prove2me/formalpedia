-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.card_le_ringKrullDim_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:08.018801+00:00
-- url     : https://prove2.me/submissions/bd156bf6-5b7a-4d8a-bca1-851204598e10

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_GermRegularParameters
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_CoordinateDimensionBound
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_sections_span_eq_maximalIdeal_with_coords
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_germ_mem_maximalIdeal_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
private theorem nontrivial_sections_of_mem (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    Nontrivial Γ(X, U) := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hs
  have := hs
  have h1 : (1 : Γ(X, U)) ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
    rw [Subsingleton.elim (1 : Γ(X, U)) 0]
    exact Ideal.zero_mem _
  exact (hU.primeIdealOf ⟨x, hx⟩).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
private theorem coord_injective (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) : Function.Injective c.coord := by
  let inst : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := c.algebra_etale hU
  have : Nontrivial Γ(X, U) := nontrivial_sections_of_mem hU x hx
  have : Module.Flat (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U) := inferInstance
  have := Module.Flat.isTorsionFree (R := MvPolynomial (ULift.{u} (Fin m)) k) (M := Γ(X, U))
  have hinj0 : Function.Injective
      (algebraMap (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, U)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective ⇑c.coordRingHom := hinj0
  intro a b hab
  have h1 : (MvPolynomial.X (ULift.up a) : MvPolynomial (ULift.{u} (Fin m)) k)
      = MvPolynomial.X (ULift.up b) := by
    apply hinj
    rw [EtaleChart.coordRingHom_X, EtaleChart.coordRingHom_X, hab]
  have h2 : (ULift.up a : ULift.{u} (Fin m)) = ULift.up b := MvPolynomial.X_injective h1
  exact congrArg ULift.down h2
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (hU : IsAffineOpen U) (c : EtaleChart p U m)
    (x : X) (hx : x ∈ U) (J : Finset (Fin m))
    (hJ : ∀ j ∈ J, c.coord j ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal) :
    (J.card : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
  classical
  obtain ⟨d, f, -, hf2, -, hd⟩ :=
    exists_sections_span_eq_maximalIdeal_with_coords hU c x hx J
      (fun j hj => (germ_mem_maximalIdeal_iff hU x hx (c.coord j)).mpr (hJ j hj))
  rw [← hd]
  rcases Finset.eq_empty_or_nonempty J with rfl | hJne
  · simp only [Finset.card_empty]
    exact_mod_cast Nat.zero_le d
  · obtain ⟨j₀, hj₀⟩ := hJne
    obtain ⟨i₀, -⟩ := hf2 j₀ hj₀
    have hch : ∀ j : Fin m, ∃ i : Fin d, j ∈ J → f i = c.coord j := by
      intro j
      by_cases hj : j ∈ J
      · obtain ⟨i, hi⟩ := hf2 j hj
        exact ⟨i, fun _ => hi⟩
      · exact ⟨i₀, fun h => absurd h hj⟩
    choose g hg using hch
    have hmap : ∀ a ∈ J, g a ∈ (Finset.univ : Finset (Fin d)) := fun a _ => Finset.mem_univ _
    have hinjOn : Set.InjOn g (J : Set (Fin m)) := by
      intro a ha b hb hab
      have h1 : c.coord a = c.coord b := by
        rw [← hg a (Finset.mem_coe.mp ha), ← hg b (Finset.mem_coe.mp hb), hab]
      exact coord_injective hU c x hx h1
    have hcard : J.card ≤ (Finset.univ : Finset (Fin d)).card :=
      Finset.card_le_card_of_injOn g hmap hinjOn
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    exact_mod_cast hcard
end FunctorialResolution.EmbeddedResolution
