-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.exists_mat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:14.282752+00:00
-- url     : https://prove2.me/submissions/96620be4-cbb0-4410-a8b5-916109773778

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
namespace Formalism.HN.QuotientRealization
theorem _root_.solution {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (T : (κ → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) (hT : Function.Injective T) :
    ∃ M : Matrix κ κ ℂ, IsUnit M.det ∧ ∀ z, Formalism.HermitianLatticesTheory.cnorm (M *ᵥ z) = ‖T z‖ := by
  classical
  have hdim : Module.finrank ℂ (LinearMap.range T) = Fintype.card κ := by
    rw [LinearMap.finrank_range_of_inj hT, Module.finrank_fintype_fun_eq_card]
  let e : LinearMap.range T ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
    ((stdOrthonormalBasis ℂ (LinearMap.range T)).reindex
      (Fintype.equivFinOfCardEq hdim.symm).symm).repr
  let f : (κ → ℂ) →ₗ[ℂ] (κ → ℂ) := (WithLp.linearEquiv 2 ℂ (κ → ℂ)).toLinearMap ∘ₗ
    e.toLinearEquiv.toLinearMap ∘ₗ T.rangeRestrict
  have hf : ∀ z, ‖(WithLp.toLp 2 (f z) : EuclideanSpace ℂ κ)‖ = ‖T z‖ := by
    intro z
    simp [f, LinearIsometryEquiv.norm_map]
  have hinj : Function.Injective f := by
    intro z w hzw
    apply hT
    have h1 : T.rangeRestrict z = T.rangeRestrict w := by
      apply e.injective
      have := congrArg (WithLp.toLp 2) hzw
      simpa [f] using this
    simpa using congrArg Subtype.val h1
  refine ⟨LinearMap.toMatrix' f, ?_, fun z => ?_⟩
  · rw [LinearMap.det_toMatrix']
    first
      | simpa using (LinearEquiv.ofInjectiveEndo f hinj).isUnit_det'
      | exact (LinearEquiv.ofInjectiveEndo f hinj).isUnit_det'
  · rw [LinearMap.toMatrix'_mulVec, Formalism.HN.PlaceOperatorNorms.cnorm_eq, hf]
end Formalism.HN.QuotientRealization
