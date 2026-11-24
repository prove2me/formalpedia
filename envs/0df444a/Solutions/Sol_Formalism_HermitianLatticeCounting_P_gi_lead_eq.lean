-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gi_lead_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:52.346798+00:00
-- url     : https://prove2.me/submissions/e1f873b5-a82c-4637-ac5c-c964cee6332a

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
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    leadingPrincipalMinor Z r = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  unfold leadingPrincipalMinor
  let e : Fin r ≃ {i : Fin (r + 1) // (i : ℕ) < r} :=
    { toFun := fun k => ⟨Fin.castSucc k, k.2⟩
      invFun := fun i => ⟨i.1, i.2⟩
      left_inv := fun k => Fin.ext rfl
      right_inv := fun i => Subtype.ext (Fin.ext rfl) }
  exact (Matrix.det_submatrix_equiv_self e _).symm
end Formalism.HermitianLatticeCounting.P
