-- Prove2me | solution 1 for CompanionTheory.FamInh.res_restrictScalars
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.125039+00:00
-- url     : https://prove2.me/submissions/67db532f-709e-4f06-b166-1ec8d4b84eac

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open CompanionTheory CompanionTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
omit [NumberField K] [NumberField L] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace CompanionTheory.FamInh
theorem _root_.solution (g : Ω ≃ₐ[L] Ω) : AlgEquiv.restrictNormalHom L (g.restrictScalars K : G K Ω) = 1 := by
  ext x
  apply (algebraMap L Ω).injective
  exact (AlgEquiv.restrictNormal_commutes (g.restrictScalars K) L x).trans (g.commutes x)
end CompanionTheory.FamInh
