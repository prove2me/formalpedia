-- Prove2me | solution 1 for Formalism.HN.DualPolygon.span_zl_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.961835+00:00
-- url     : https://prove2.me/submissions/6a623828-9939-40e3-b7d5-5c0b6244bb88

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
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis____9cab7951c4f4
import Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (hN : N.FG)
    (hsp : Submodule.span K (N : Set V) = ⊤) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
      Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) = ⊤ := by
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX N hN
  have : DiscreteTopology (zl (Formalism.HermitianLatticesTheory.realize b X) N) := hlat.2
  let bz := Module.finBasis ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N)
  have hv := Formalism.F.linearIndependent_coe_basis''' _ bz
  have hspZ := Formalism.F.span_range_coe_basis' _ bz
  apply Submodule.eq_top_of_finrank_eq
  rw [← hspZ, Submodule.span_span_of_tower, finrank_span_eq_card hv, Fintype.card_fin,
    finrank_euclideanSpace]
  have h1 : Module.finrank ℤ (zl (Formalism.HermitianLatticesTheory.realize b X) N) = rk (Formalism.HermitianLatticesTheory.realize b X) N := rfl
  have h2 : rkK N = Fintype.card ι := by
    unfold rkK; rw [hsp, finrank_top, finrank_eq_card_basis b]
  rw [h1, hrk, h2, sizeMu_finrank_eq, nPl]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring
end Formalism.HN.DualPolygon
