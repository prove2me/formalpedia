-- Prove2me | solution 1 for Derivation.exists_derivation_mul_eq_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:57.971276+00:00
-- url     : https://prove2.me/submissions/d8c16239-77eb-4272-8096-baa575a27e72

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DerivationLocalization
import Theorems.Thm_Derivation_exists_derivation_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v w x
variable {R : Type u} {S : Type v} {S' : Type w} {N : Type x}
variable [CommRing R] [CommRing S] [CommRing S'] [AddCommGroup N]
variable [Algebra R S] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']
variable [Module R N] [Module S N] [Module S' N]
variable [IsScalarTower R S N] [IsScalarTower S S' N] [IsScalarTower R S' N]
open Derivation
namespace Derivation
theorem _root_.solution (M : Submonoid S) [IsLocalization M S']
    [Module.FinitePresentation S (KaehlerDifferential R S)] (D : Derivation R S' S') :
    ∃ (m : M) (D₀ : Derivation R S S), ∀ s : S,
      algebraMap S S' (m : S) * D (algebraMap S S' s) = algebraMap S S' (D₀ s) := by
  obtain ⟨m, D₀, h⟩ := exists_derivation_mul_eq (S' := S') M (D.compAlgebraMap S)
  exact ⟨m, D₀, fun s => h s⟩
end Derivation
