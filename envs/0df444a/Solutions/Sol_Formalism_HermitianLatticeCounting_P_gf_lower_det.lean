-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_lower_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:42.616259+00:00
-- url     : https://prove2.me/submissions/8f7301b9-15dd-4e46-b446-f3ff35d51689

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (ρ : α → Fin d) (hmono : StrictMono ρ) (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) :
    (l.submatrix ρ ρ).det = 1 := by
  unfold IsLowerUnitriangular at hl
  rw [Matrix.det_of_lowerTriangular (l.submatrix ρ ρ) (fun a b hab => hl.2 _ _ (hmono hab))]
  simp [Matrix.submatrix_apply, hl.1]
end Formalism.HermitianLatticeCounting.P
