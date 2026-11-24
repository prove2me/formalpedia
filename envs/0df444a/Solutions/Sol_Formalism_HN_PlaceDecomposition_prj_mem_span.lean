-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.prj_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:03.113592+00:00
-- url     : https://prove2.me/submissions/b4d9632f-4509-422d-8fe7-b72e2ff9da02

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_dense_comb
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_realize_comb

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))
    (hw : w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))) :
    prj v w ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  have key : Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ≤
      (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))).comap (prj v) := by
    rw [Submodule.span_le]
    intro s hs
    have hs' : s ∈ (N.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b X)) := hs
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hs'
    show prj v (Formalism.HermitianLatticesTheory.realize b X x) ∈ Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
    obtain ⟨r, hr⟩ := dense_comb K (fun u => if u = v then (1 : ℂ) else 0)
    rw [prj_realize_comb b X v r hr x]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact AddSubgroup.mem_map.2 ⟨_, N.smul_mem _ hx, rfl⟩
  exact key hw
end Formalism.HN.PlaceDecomposition
