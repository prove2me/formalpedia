-- Prove2me | solution 1 for Formalism.HN.DualPolygon.sat_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:19.078794+00:00
-- url     : https://prove2.me/submissions/ff9093c4-03ad-440c-a839-ce9ff2e692b6

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
import Theorems.Thm_Formalism_F_saturProps
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_real_saturation_property
import Theorems.Thm_Formalism_HN_saturation_basic_properties
import Theorems.Thm_Formalism_HN_shiftInv_zl_mono


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
    (hX : ∀ v, IsUnit (X v).det) (A : Submodule (𝓞 K) V) (hA : A.FG) (N : Submodule (𝓞 K) V)
    (hNA : N ≤ A) :
    ∃ N', N ≤ N' ∧ IsSat (Formalism.HermitianLatticesTheory.realize b X) A N' ∧
      Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N ∧
      deg (Formalism.HermitianLatticesTheory.realize b X) N ≤ deg (Formalism.HermitianLatticesTheory.realize b X) N' := by
  obtain ⟨hlat, -, -⟩ := place_lattice_structure K V ι b X hX A hA
  obtain ⟨N', h1, h2, h3⟩ := real_saturation_property (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A N hlat hNA
  obtain ⟨s1, -, s3⟩ := Formalism.F.saturProps _ (zl (Formalism.HermitianLatticesTheory.realize b X) A)
    (zl (Formalism.HermitianLatticesTheory.realize b X) N) hlat.2 (shiftInv_zl_mono (Formalism.HermitianLatticesTheory.realize b X) hNA)
  have hrk : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N' = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N := by
    unfold Formalism.HN.rk; rw [h3]; exact s3
  have hSB := saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) A hlat
  exact ⟨N', h1, ⟨h2, by rw [h3]; exact s1⟩, hrk, (hSB.2.1 N N' h1 h2).2 hrk.symm⟩
end Formalism.HN.DualPolygon
