-- Prove2me | solution 1 for Erdos180.symplecticLineNormalizer_map_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:10:00.745012+00:00
-- url     : https://prove2.me/submissions/a0fe0cb6-bec6-43a7-8cf0-bc683dfb6ded

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace Erdos180

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]

lemma symplecticLineNormalizer_apply_right
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1)
    (y : M.1) :
    symplecticLineNormalizer K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] := by
  change
    symplecticLineCoordinateEquiv K L M hLM
        (y : SymplecticVector K) =
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1]
  have h := symplecticLineCoordinateEquiv_apply_add K L M hLM
    (0 : L.1) y
  simpa using h

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (L M : SymplecticLine K)
    (hLM : Disjoint L.1 M.1) :
    symplecticAutomorphismLine K
        (symplecticLineNormalizer K L M hLM) M =
      symplecticVerticalLine K := by
  apply Subtype.ext
  change
    M.1.map (symplecticLineNormalizer K L M hLM).toLinearEquiv.toLinearMap =
      LinearMap.range (symplecticVerticalLinearMap K)
  apply le_antisymm
  · intro v hv
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hv
    refine ⟨symplecticLineDualCoordinates K L M hLM ⟨y, hy⟩, ?_⟩
    simpa [symplecticVerticalLinearMap] using
      (symplecticLineNormalizer_apply_right K L M hLM
        (⟨y, hy⟩ : M.1)).symm
  · intro v hv
    obtain ⟨z, rfl⟩ := hv
    let y : M.1 :=
      (symplecticLineDualCoordinates K L M hLM).symm z
    refine Submodule.mem_map.mpr
      ⟨(y : SymplecticVector K), y.2, ?_⟩
    change
      symplecticLineNormalizer K L M hLM
          (y : SymplecticVector K) =
        symplecticVerticalLinearMap K z
    rw [symplecticLineNormalizer_apply_right]
    change
      ![0, symplecticLineDualCoordinates K L M hLM y 0,
        0, symplecticLineDualCoordinates K L M hLM y 1] =
        ![0, z 0, 0, z 1]
    have hy : symplecticLineDualCoordinates K L M hLM y = z :=
      (symplecticLineDualCoordinates K L M hLM).apply_symm_apply z
    rw [hy]
