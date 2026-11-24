-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.realize_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:22.324362+00:00
-- url     : https://prove2.me/submissions/ba189e29-d10a-40fd-b039-d12b5516ceeb

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

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
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (N : Submodule (𝓞 K) V)
    {x : V} (hx : x ∈ N) :
    Formalism.HermitianLatticesTheory.realize b X x ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) N : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  first
    | exact Submodule.subset_span ⟨x, hx, rfl⟩
    | exact Submodule.subset_span (AddSubgroup.mem_map.2 ⟨x, hx, rfl⟩)
    | exact Submodule.subset_span (Set.mem_image_of_mem _ hx)
end Formalism.HN.PlaceDecomposition
