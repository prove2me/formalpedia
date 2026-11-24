-- Prove2me | solution 1 for Formalism.HN.DualPolygon.corr_R
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:06.440848+00:00
-- url     : https://prove2.me/submissions/a38cda96-35e3-47f1-8bdc-3e3043ae5715

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
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_unit
import Theorems.Thm_Formalism_HN_DualPolygon_dualLat_fg
import Theorems.Thm_Formalism_HN_DualPolygon_key_lemma
import Theorems.Thm_Formalism_HN_DualPolygon_sat_of_ann
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties


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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) (R : Submodule (𝓞 K) (Module.Dual K V))
    (hR : R ≤ dualLat A) : ∃ N, IsSat (Formalism.HermitianLatticesTheory.realize b X) A N ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
        Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) ∧
      deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R ≤
        deg (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hX' := dualFrame_unit X hX
  have hdfg := dualLat_fg A hsp
  obtain ⟨hlat', -, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' (dualLat A) hdfg
  have hSB' := saturation_basic_properties (𝓞 K) (Module.Dual K V) _ _ (dualLat A) hlat'
  obtain ⟨N, hN, hRN, hdim⟩ := sat_of_ann b X hX A hA hsp R hR
  obtain ⟨hdimN, -⟩ := key_lemma b X hX A hA hsp N hN
  have hRfg : R.FG := Submodule.FG.of_le hdfg hR
  have hRNfg : (dualLat A ⊓ annO N).FG := Submodule.FG.of_le hdfg inf_le_left
  obtain ⟨-, r1, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' R hRfg
  obtain ⟨-, r2, -⟩ := place_lattice_structure K _ ι b.dualBasis (dualFrame X) hX' _ hRNfg
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) R =
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X)) (dualLat A ⊓ annO N) := by
    calc _ = finrank ℚ K * rkK R := r1
      _ = finrank ℚ K * rkK (dualLat A ⊓ annO N) := by congr 1; omega
      _ = _ := r2.symm
  exact ⟨N, hN, hrk, (hSB'.2.1 R _ hRN inf_le_left).2 hrk⟩
end Formalism.HN.DualPolygon
