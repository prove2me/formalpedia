-- Prove2me | solution 1 for Formalism.HN.sizeIneq_span_inf_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:24.952599+00:00
-- url     : https://prove2.me/submissions/1cd734a8-8088-484a-9aef-be303b24d36e

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
import Theorems.Thm_Formalism_HN_sizeIneq_exists_mul_mem

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
theorem _root_.solution (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨hxA, hxk⟩
    exact ⟨Submodule.subset_span hxA, hxk⟩
  · rintro x ⟨hxS, hxk⟩
    obtain ⟨d, hd, hdx⟩ := sizeIneq_exists_mul_mem A x hxS
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := by
      intro h0
      exact hd (FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero]))
    have hmem : d • x ∈ (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine ⟨hdx, ?_⟩
      show φ (d • x) = 0
      rw [← algebraMap_smul K d x, map_smul, LinearMap.mem_ker.mp hxk, smul_zero]
    have hx : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end Formalism.HN
