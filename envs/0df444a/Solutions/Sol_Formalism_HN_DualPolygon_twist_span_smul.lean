-- Prove2me | solution 1 for Formalism.HN.DualPolygon.twist_span_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:01.353833+00:00
-- url     : https://prove2.me/submissions/e8808090-0343-4417-b857-3a9fdd5fc492

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
attribute [local instance] Ideal.Quotient.field
variable {K W : Type} [Field K] [NumberField K]
    [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [FiniteDimensional K W]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (X : Submodule (𝓞 K) W) (𝔞 : Ideal (𝓞 K)) (h : 𝔞 ≠ ⊥) :
    Submodule.span K ((𝔞 • X : Submodule (𝓞 K) W) : Set W) = Submodule.span K (X : Set W) := by
  apply le_antisymm
  · exact Submodule.span_mono (Submodule.smul_le_right)
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hmem : α • x ∈ 𝔞 • X := Submodule.smul_mem_smul hα hx
    have hK : (algebraMap (𝓞 K) K α) ≠ 0 := by
      intro h0
      exact hα0 (FaithfulSMul.algebraMap_injective (𝓞 K) K (by simpa using h0))
    have hx' : x = (algebraMap (𝓞 K) K α)⁻¹ • (α • x) := by
      rw [← algebraMap_smul K α x, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [SetLike.mem_coe, hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end Formalism.HN.DualPolygon
