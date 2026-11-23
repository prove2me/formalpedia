-- Prove2me | solution 1 for CompanionTheory.FamInh.coe_res_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:08.014729+00:00
-- url     : https://prove2.me/submissions/54fe9cb6-5347-4b85-bd7f-518cb76d86e1

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
theorem _root_.solution (σ : G K Ω) (x : 𝓞 L) :
    algebraMap L Ω ((AlgEquiv.restrictNormalHom L σ • x : 𝓞 L) : L) = σ (algebraMap L Ω (x : L)) :=
  AlgEquiv.restrictNormal_commutes σ L (x : L)
end CompanionTheory.FamInh
