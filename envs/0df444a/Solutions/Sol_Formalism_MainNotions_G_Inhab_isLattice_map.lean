-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.isLattice_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:17.350851+00:00
-- url     : https://prove2.me/submissions/fd343f7a-c65c-4dfa-a69b-290743476cf5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_P2M_Formalism_MainNotions_G_Inhab_map_colSpan__20236f61806d
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial
variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (A : GL (Fin k) K) {L : Submodule R (Fin k → K)} (hL : IsLattice R L) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) := by
  obtain ⟨g, hg, rfl⟩ := hL
  refine ⟨(A : Matrix (Fin k) (Fin k) K) * g, ?_, map_colSpan' A g⟩
  rw [Matrix.det_mul]
  exact (Matrix.isUnits_det_units A).mul hg
end Formalism.MainNotions.G.Inhab
