-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mapToLocalization_mem_tangentDerivations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:07.858069+00:00
-- url     : https://prove2.me/submissions/69ece4cd-c1b7-4b27-ad4e-a7383bb92802

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
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
private theorem derivation_mem_map_of_forall_mem {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra R B]
    (D' : Derivation R B B) {P : Ideal A}
    (hgen : ∀ p ∈ P, D' (algebraMap A B p) ∈ P.map (algebraMap A B)) :
    ∀ x ∈ P.map (algebraMap A B), D' x ∈ P.map (algebraMap A B) := by
  intro x hx
  have hx' : x ∈ Ideal.span ((algebraMap A B) '' (P : Set A)) := hx
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨p, hp, rfl⟩ := hy
      exact hgen p hp
  | zero => simp
  | add y z hy hz ihy ihz =>
      have h : D' (y + z) = D' y + D' z := by simp
      rw [h]
      exact Ideal.add_mem _ ihy ihz
  | smul a y hy ih =>
      have hy' : y ∈ P.map (algebraMap A B) := hy
      rw [smul_eq_mul, D'.leibniz]
      simp only [smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ hy')
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k]
variable {S : Type*} [CommRing S] [Algebra k S]
variable {S' : Type*} [CommRing S'] [Algebra S S'] [Algebra k S'] [IsScalarTower k S S']
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (M : Submonoid S) [IsLocalization M S']
    {P : Ideal S} {D : Derivation k S S} (hD : D ∈ tangentDerivations k P) :
    (D.mapToLocalization (S' := S') M) ∈
      tangentDerivations k (P.map (algebraMap S S')) := by
  have hD' := (mem_tangentDerivations k P D).mp hD
  rw [mem_tangentDerivations]
  refine derivation_mem_map_of_forall_mem (D.mapToLocalization (S' := S') M) ?_
  intro p hp
  rw [Derivation.mapToLocalization_algebraMap]
  exact Ideal.mem_map_of_mem _ (hD' p hp)
end FunctorialResolution.EmbeddedResolution
