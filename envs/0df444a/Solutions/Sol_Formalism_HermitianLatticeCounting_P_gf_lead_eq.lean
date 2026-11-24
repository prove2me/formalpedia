-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_lead_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:24.133836+00:00
-- url     : https://prove2.me/submissions/2ba9de29-a76d-451e-857c-f81f53e01af1

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
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} (Z : Matrix (Fin d) (Fin d) R) (q : ℕ) (h : q ≤ d) :
    leadingPrincipalMinor Z q = (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  unfold leadingPrincipalMinor
  let e : Fin q ≃ {i : Fin d // (i : ℕ) < q} :=
    { toFun := fun k => ⟨Fin.castLE h k, k.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun i => Subtype.ext (Fin.ext rfl) }
  exact (Matrix.det_submatrix_equiv_self e _).symm
end Formalism.HermitianLatticeCounting.P
