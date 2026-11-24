-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.tv_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:10.355795+00:00
-- url     : https://prove2.me/submissions/39d546b2-0878-4a2f-8c2f-0d3db38c6aea

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_finrank_pv
import Theorems.Thm_Formalism_HN_QuotientRealization_pv_top
import Theorems.Thm_Formalism_HN_QuotientRealization_proj_eq_tv

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
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (hX : ∀ v, IsUnit (X v).det) (hc : ∀ k, U.mkQ (c k) = b'' k)
    (v : InfinitePlace K) : Function.Injective (tv b X U c v) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hle : (pv b X U v)ᗮ ≤ LinearMap.range (tv b X U c v) := by
    intro w hw
    have hw' : (pv b X U v)ᗮ.starProjection w = w := Submodule.starProjection_eq_self_iff.2 hw
    have htop : w ∈ pv b X ⊤ v := by rw [pv_top b X hX v]; trivial
    have hmap : (pv b X ⊤ v).map
        ((pv b X U v)ᗮ.starProjection : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι).toLinearMap ≤
        LinearMap.range (tv b X U c v) := by
      unfold pv
      rw [Submodule.map_span_le]
      rintro _ ⟨y, -, rfl⟩
      exact LinearMap.mem_range.2 ⟨_, (proj_eq_tv b X U b'' c hc v y).symm⟩
    rw [← hw']
    exact hmap ⟨w, htop, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_finrank_orthogonal (pv b X U v)
  rw [finrank_pv b X hX, finrank_euclideanSpace] at h2
  have h3 := Submodule.finrank_quotient_add_finrank U
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b''] at h3
  have h4 := LinearMap.finrank_range_add_finrank_ker (tv b X U c v)
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have h5 : finrank ℂ (LinearMap.ker (tv b X U c v)) = 0 := by omega
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.1 h5
end Formalism.HN.QuotientRealization
