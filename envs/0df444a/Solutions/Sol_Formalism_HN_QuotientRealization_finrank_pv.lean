-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.finrank_pv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:22.749462+00:00
-- url     : https://prove2.me/submissions/527e3e2d-2d33-4cdc-8285-50e09f70bee8

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_span_complex


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (U : Submodule K V) (v : InfinitePlace K) :
    finrank ℂ (pv b X U v) = finrank K U := by
  have h : pv b X U v = (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (U : Set V))).map
      ((WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι) := by
    rw [Submodule.map_span, Set.image_image]; rfl
  rw [h, LinearEquiv.finrank_map_eq]
  have := PlaceDecomposition.finrank_span_complex b X hX (U.restrictScalars (𝓞 K)) v
  rw [Submodule.coe_restrictScalars] at this
  rw [this, rkK, Submodule.coe_restrictScalars, Submodule.span_eq]
end Formalism.HN.QuotientRealization
