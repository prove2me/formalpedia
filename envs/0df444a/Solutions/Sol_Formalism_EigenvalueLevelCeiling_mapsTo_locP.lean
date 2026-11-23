-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.mapsTo_locP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:26.621486+00:00
-- url     : https://prove2.me/submissions/9f0588f7-e129-48e9-b7c1-4dbfa6b54a65

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_OrthogonalityOfMackey
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LemmaGG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (f : W →ₗ[R] W) (X Y : Submodule R W) (h : ∀ x ∈ X, f x ∈ Y) :
    ∀ x ∈ Formalism.HermitianLatticesTheory.localization₂ p X, f x ∈ Formalism.HermitianLatticesTheory.localization₂ p Y := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, by rw [← map_smul]; exact h _ hx⟩
end Formalism.EigenvalueLevelCeiling
