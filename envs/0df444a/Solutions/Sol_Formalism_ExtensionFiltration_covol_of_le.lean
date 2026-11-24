-- Prove2me | solution 1 for Formalism.ExtensionFiltration.covol_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:19.7438+00:00
-- url     : https://prove2.me/submissions/0557dd17-2b15-47a6-b81f-88c1413e732d

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_DescentSlope
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_injective
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_shiftInv_zl_mono
import Theorems.Thm_Formalism_RankSupermodularCovolume_covol_eq_relIndex_mul_covol


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
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open scoped Pointwise
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N M : Submodule (𝓞 K) V) (hN : N.FG) (hM : M.FG) (hle : N ≤ M)
    (hrk : rkK N = rkK M) :
    Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) N) =
      (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) * Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
  obtain ⟨hMlat, hrkM, -⟩ := place_lattice_structure K V ι b X hX M hM
  obtain ⟨-, hrkN, -⟩ := place_lattice_structure K V ι b X hX N hN
  have := hMlat.2
  have hzl : zl (Formalism.HermitianLatticesTheory.realize b X) N ≤ zl (Formalism.HermitianLatticesTheory.realize b X) M := shiftInv_zl_mono _ hle
  have hrkeq : Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) N) = Formalism.F.rk (zl (Formalism.HermitianLatticesTheory.realize b X) M) := by
    have h1 : Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) N = Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) M := by
      rw [hrkN, hrkM, hrk]
    exact h1
  have hcov := Formalism.RankSupermodularCovolume.covol_eq_relIndex_mul_covol _ _ hzl hrkeq
  have hinj := Formalism.HN.PlaceLattice.realize_injective b X hX
  have hidx : (zl (Formalism.HermitianLatticesTheory.realize b X) N).toAddSubgroup.relIndex
      (zl (Formalism.HermitianLatticesTheory.realize b X) M).toAddSubgroup = N.toAddSubgroup.relIndex M.toAddSubgroup := by
    simp only [zl, AddSubgroup.toIntSubmodule_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  rw [hcov, hidx]
end Formalism.ExtensionFiltration
