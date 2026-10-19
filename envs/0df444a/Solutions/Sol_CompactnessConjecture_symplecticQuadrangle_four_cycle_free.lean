-- Prove2me | solution 1 for CompactnessConjecture.symplecticQuadrangle_four_cycle_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/e9859b3d-0c7a-47ef-9dcc-3739987667f2

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_symplecticQuadrangle_common_neighbor_unique

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution :
    (SimpleGraph.cycleGraph 4).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h21 : (symplecticQuadrangle K).Adj (copy 2) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h03 : (symplecticQuadrangle K).Adj (copy 0) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h02 : copy 0 ≠ copy 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (copy.injective h)
  have h13 : copy 1 = copy 3 :=
    symplecticQuadrangle_common_neighbor_unique K h02 h01 h21 h03 h23
  exact (by decide : (1 : Fin 4) ≠ 3) (copy.injective h13)
end CompactnessConjecture
