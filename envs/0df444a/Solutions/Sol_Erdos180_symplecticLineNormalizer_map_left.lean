-- Prove2me | solution 1 for Erdos180.symplecticLineNormalizer_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:08:58.829103+00:00
-- url     : https://prove2.me/submissions/c02c1a46-3bf8-4235-82bf-44f5d4fb73e0

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticLineNormalizer_apply_left
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (x : L.1) :
    symplecticLineNormalizer K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (x : SymplecticVector K) =
      ![(symplecticLineBasis K L).equivFun x 0, 0,
        (symplecticLineBasis K L).equivFun x 1, 0]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    x (0 : M.1)
  simpa [standardSymplecticForm] using h

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) L =
      symmetricGraphLine K 0 0 0 := by
  apply Subtype.ext
  change
    L.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symmetricGraphLinearMap K 0 0 0)
  apply le_antisymm
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨(symplecticLineBasis K L).equivFun ⟨x, hx⟩, ?_⟩
    simpa [symmetricGraphLinearMap, symmetricGraphVector] using
      (symplecticLineNormalizer_apply_left K L M hLM
        (⟨x, hx⟩ : L.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let x : L.1 := (symplecticLineBasis K L).equivFun.symm z
    refine Submodule.mem_map.mpr
      ⟨(x : SymplecticVector K), x.2, ?_⟩
    simpa [x, symmetricGraphLinearMap, symmetricGraphVector] using
      symplecticLineNormalizer_apply_left K L M hLM x
