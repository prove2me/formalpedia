-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_len_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:18.632372+00:00
-- url     : https://prove2.me/submissions/ebc82fb3-204f-4478-b4e1-0c00f3cf1858

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (f : V →ₗ[R] V') (hf : Function.Injective f) (X Y : Submodule R V) :
    Module.length R (↥(X.map f) ⧸ (Y.map f).comap (X.map f).subtype) =
      Module.length R (↥X ⧸ Y.comap X.subtype) := by
  symm
  apply LinearEquiv.length_eq
  refine Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf X) ?_
  apply le_antisymm
  · rintro _ ⟨⟨x, hx⟩, hxY, rfl⟩
    exact ⟨x, hxY, rfl⟩
  · rintro ⟨z, hz⟩ ⟨y, hy, hyz⟩
    obtain ⟨x, hx, hxz⟩ := hz
    have hxy : x = y := hf (hxz.trans hyz.symm)
    subst hxy
    refine ⟨⟨x, hx⟩, hy, ?_⟩
    apply Subtype.ext
    exact hxz
end Formalism.EigenvalueLevelCeiling
