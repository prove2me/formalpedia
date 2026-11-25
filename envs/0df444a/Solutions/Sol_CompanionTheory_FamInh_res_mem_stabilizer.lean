-- Prove2me | solution 1 for CompanionTheory.FamInh.res_mem_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:39.876121+00:00
-- url     : https://prove2.me/submissions/bd3a563d-53ad-470d-bbf8-f57d1903a7d2

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_CompanionTheory_AutomorphicTheory_PlaceSeparation_ArtinA
import Theorems.Thm_CompanionTheory_FamInh_coe_res_smul

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
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
omit [IsAlgClosure K Ω] [IsAlgClosure L Ω]
namespace CompanionTheory.FamInh
theorem _root_.solution (hw : IsPlaceOver A w) {σ : G K Ω} (hσ : σ ∈ Dec (F := K) A) :
    AlgEquiv.restrictNormalHom L σ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ← hw, ← hw, coe_res_smul,
    valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ)]
end CompanionTheory.FamInh
