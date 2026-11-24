-- Prove2me | solution 1 for Formalism.HN.sizeIneq_rk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.348424+00:00
-- url     : https://prove2.me/submissions/79258028-4085-483f-80a6-6cd7b3f4310a

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Theorems.Thm_Formalism_HN_sizeIneq_span_inf_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
namespace Formalism.HN
theorem _root_.solution [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by
  unfold rkK
  set S := Submodule.span K (A : Set V) with hS
  have h1 : Submodule.span K ((A.map (φ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      S.map φ := by
    rw [Submodule.map_coe, hS, Submodule.map_span]
    rfl
  rw [h1, sizeIneq_span_inf_ker]
  have := (φ.domRestrict S).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at this
  rw [← this, ← Submodule.map_comap_subtype S (LinearMap.ker φ)]
  congr 1
  exact (Submodule.equivMapOfInjective _ S.injective_subtype _).finrank_eq.symm
end Formalism.HN
