-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.isLattice_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:49.55795+00:00
-- url     : https://prove2.me/submissions/224ba7e1-f761-4980-a48a-83337707b95d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataForm
import Theorems.Thm_Formalism_MainNotions_G_Inhab_isLattice_map
import Theorems.Thm_Formalism_MainNotions_G_Inhab_map_map_inv

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
theorem _root_.solution (A : GL (Fin k) K) (L : Submodule R (Fin k → K)) :
    IsLattice R (L.map ((Matrix.mulVecLin (A : Matrix (Fin k) (Fin k) K)).restrictScalars R)) ↔ IsLattice R L := ⟨fun h => by
    have h' := isLattice_map (A⁻¹) h
    rwa [map_map_inv] at h', isLattice_map A⟩
end Formalism.MainNotions.G.Inhab
