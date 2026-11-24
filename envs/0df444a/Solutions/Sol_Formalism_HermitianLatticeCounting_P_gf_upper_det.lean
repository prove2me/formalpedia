-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_upper_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:51.389502+00:00
-- url     : https://prove2.me/submissions/0a34eeac-4bb4-4a54-aeeb-2bca09f0758c

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
    (ρ : α → Fin d) (hmono : StrictMono ρ) (u : Matrix (Fin d) (Fin d) R) (hu : IsUpperUnitriangular u) :
    (u.submatrix ρ ρ).det = 1 := by
  unfold IsUpperUnitriangular at hu
  rw [Matrix.det_of_upperTriangular (M := u.submatrix ρ ρ) (fun a b hab => hu.2 _ _ (hmono hab))]
  simp [Matrix.submatrix_apply, hu.1]
end Formalism.HermitianLatticeCounting.P
