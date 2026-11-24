-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ge_principal_minor_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:50.38081+00:00
-- url     : https://prove2.me/submissions/da337d7b-c4f1-45b5-ba4b-15fc1d12322d

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
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix Polynomial
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {K : Type*} [CommRing K] {i n : ℕ} (A : Matrix (Fin i) (Fin n) K)
    (B : Matrix (Fin n) (Fin i) K) (S : Finset (Fin n)) (hS : S.card = i) :
    ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det
      = (B.submatrix (S.orderEmbOfFin hS) id).det * (A.submatrix id (S.orderEmbOfFin hS)).det := by
  rw [← det_mul, ← Matrix.det_submatrix_equiv_self (S.orderIsoOfFin hS).toEquiv]
  congr 1
end Formalism.HermitianLatticeCounting.P
