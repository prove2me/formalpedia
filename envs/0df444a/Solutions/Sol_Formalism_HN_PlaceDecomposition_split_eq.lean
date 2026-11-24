-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.split_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:16.478482+00:00
-- url     : https://prove2.me/submissions/a38d91b8-0313-4785-82c4-0ba839d185c1

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_mem
import Theorems.Thm_Formalism_HN_PlaceDecomposition_sum_prj
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_mem_span

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
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
variable [DecidableEq (InfinitePlace K)]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) =
      ⨆ v, Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v := by
  apply le_antisymm
  · intro w hw
    rw [← sum_prj w]
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.mem_iSup_of_mem v (Submodule.mem_inf.2 ⟨prj_mem_span b X N v w hw, prj_mem v w⟩)
  · exact iSup_le fun v => inf_le_left
end Formalism.HN.PlaceDecomposition
