-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_mem_tangentDerivations_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:48:46.870337+00:00
-- url     : https://prove2.me/submissions/27d56467-d42c-442e-be1d-ddb23b42fa67

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Theorems.Thm_Derivation_exists_derivation_mul_eq_of_isLocalization
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mem_tangentDerivations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap


section
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
private theorem derivation_smul_apply {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (c : A) (D₀ : Derivation R A A) (x : A) : (c • D₀) x = c * D₀ x := rfl
private theorem mul_derivation_mem_of_span_eq {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {G : Set A} {P : Ideal A} (hP : Ideal.span G = P) (D₀ : Derivation R A A)
    (c : A) (hG : ∀ g ∈ G, c * D₀ g ∈ P) : ∀ x ∈ P, c * D₀ x ∈ P := by
  intro x hx
  rw [← hP] at hx
  induction hx using Submodule.span_induction with
  | mem g hg => exact hG g hg
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D₀ (y + z) = D₀ y + D₀ z := by simp
      rw [h, mul_add]
      exact P.add_mem ihy ihz
  | smul a y hy ih =>
      have hyP : y ∈ P := by rw [← hP]; exact hy
      rw [smul_eq_mul, D₀.leibniz]
      simp only [smul_eq_mul, mul_add]
      refine P.add_mem ?_ ?_
      · have h1 : c * (a * D₀ y) = a * (c * D₀ y) := by ring
        rw [h1]
        exact P.mul_mem_left a ih
      · exact P.mul_mem_left c (P.mul_mem_right (D₀ a) hyP)
private theorem exists_mem_mul_algebraMap_eq_of_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (J : Ideal A) {x : B}
    (hx : x ∈ J.map (algebraMap A B)) :
    ∃ (y : A) (t : M), y ∈ J ∧ x * algebraMap A B (t : A) = algebraMap A B y := by
  obtain ⟨u, hu⟩ := (IsLocalization.mem_map_algebraMap_iff (M := M) (S := B)).mp hx
  exact ⟨u.1, u.2, u.1.2, hu⟩
private theorem exists_mul_mem_of_algebraMap_mem_map {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (P : Ideal A) {y : A}
    (hy : algebraMap A B y ∈ P.map (algebraMap A B)) :
    ∃ m : M, (m : A) * y ∈ P := by
  obtain ⟨p, t, hp, h⟩ := exists_mem_mul_algebraMap_eq_of_mem_map M P hy
  have h2 : algebraMap A B (y * (t : A)) = algebraMap A B p := by
    rw [map_mul]; linear_combination h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := M) (S := B)).mp h2
  refine ⟨c * t, ?_⟩
  have heq : ((c * t : M) : A) * y = (c : A) * p := by
    push_cast
    linear_combination hc
  rw [heq]
  exact P.mul_mem_left _ hp
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential k S)]
    {P : Ideal S} (hP : P.FG) (D : Derivation k S' S')
    (hD : D ∈ tangentDerivations k (P.map (algebraMap S S'))) :
    ∃ (m : M) (D₁ : Derivation k S S), D₁ ∈ tangentDerivations k P ∧
      ∀ s : S, algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₁ s) := by
  have hDt := (mem_tangentDerivations k (P.map (algebraMap S S')) D).mp hD
  obtain ⟨m₀, D₀, hD₀⟩ :=
    Derivation.exists_derivation_mul_eq_of_isLocalization (S' := S') M D
  obtain ⟨G, hG⟩ := hP
  have key : ∀ g : S, ∃ n : M, g ∈ G → (n : S) * D₀ g ∈ P := by
    intro g
    by_cases hg : g ∈ G
    · have hgP : g ∈ P := by
        rw [← hG]
        exact Ideal.subset_span (Finset.mem_coe.mpr hg)
      have h1 : algebraMap S S' g ∈ P.map (algebraMap S S') := Ideal.mem_map_of_mem _ hgP
      have h2 : D (algebraMap S S' g) ∈ P.map (algebraMap S S') := hDt _ h1
      have h3 : algebraMap S S' (D₀ g) ∈ P.map (algebraMap S S') := by
        rw [← hD₀ g]
        exact Ideal.mul_mem_left _ _ h2
      obtain ⟨n, hn⟩ := exists_mul_mem_of_algebraMap_mem_map M P h3
      exact ⟨n, fun _ => hn⟩
    · exact ⟨1, fun h => absurd h hg⟩
  choose f hf using key
  obtain ⟨c, hcM, hcP⟩ : ∃ c : S, c ∈ M ∧ ∀ g ∈ G, c * D₀ g ∈ P := by
    refine ⟨Finset.prod G (fun g => ((f g : S))),
      Submonoid.prod_mem M (fun g _ => (f g).2), ?_⟩
    intro g hg
    obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun g => ((f g : S))) hg
    have h4 : ((f g : S)) * r * D₀ g = r * (((f g : S)) * D₀ g) := by ring
    rw [hr, h4]
    exact P.mul_mem_left _ (hf g hg)
  refine ⟨⟨c * (m₀ : S), M.mul_mem hcM m₀.2⟩, c • D₀, ?_, ?_⟩
  · have hgen : ∀ g ∈ (↑G : Set S), c * D₀ g ∈ P := fun g hg => hcP g (Finset.mem_coe.mp hg)
    rw [mem_tangentDerivations]
    intro x hx
    have h := mul_derivation_mem_of_span_eq hG D₀ c hgen x hx
    rw [derivation_smul_apply]
    exact h
  · intro s
    show algebraMap S S' (c * (m₀ : S)) * D (algebraMap S S' s)
        = algebraMap S S' ((c • D₀) s)
    rw [derivation_smul_apply, map_mul, map_mul, mul_assoc, hD₀ s]
end FunctorialResolution.EmbeddedResolution
