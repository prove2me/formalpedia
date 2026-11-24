-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.piece_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:21.407611+00:00
-- url     : https://prove2.me/submissions/9a48ceb1-6aeb-4a7d-bc7a-dec478b9fb5a

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_mem
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_of_mem
import Theorems.Thm_Formalism_HN_PlaceDecomposition_realize_mem
import Theorems.Thm_Formalism_HN_PlaceDecomposition_prj_realize
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
  [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace K)]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v =
      (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨hwS, hwP⟩ := Submodule.mem_inf.1 hw
    rw [← prj_of_mem v w hwP]
    have key : Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ≤
        ((Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v)).comap (prj v) := by
      rw [Submodule.span_le]
      intro s hs
      have hs' : s ∈ (N.toAddSubgroup.map (Formalism.HermitianLatticesTheory.realize b X)) := hs
      obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hs'
      show prj v (Formalism.HermitianLatticesTheory.realize b X x) ∈
        (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).map (psi v)
      rw [prj_realize]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, hx, rfl⟩)
    exact key hwS
  · rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [← prj_realize]
    exact Submodule.mem_inf.2 ⟨prj_mem_span b X N v _ (realize_mem b X N hx), prj_mem v _⟩
end Formalism.HN.PlaceDecomposition
