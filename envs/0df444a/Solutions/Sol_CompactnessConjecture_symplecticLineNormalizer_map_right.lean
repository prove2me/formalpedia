-- Prove2me | solution 1 for CompactnessConjecture.symplecticLineNormalizer_map_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/bb11cad1-124d-4f3b-9376-cd6d19b63ea2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticLineNormalizer_apply_right

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
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
end CompactnessConjecture
