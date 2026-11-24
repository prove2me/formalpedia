-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ge_coeff_top_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:50.022623+00:00
-- url     : https://prove2.me/submissions/772aa379-29fb-4f1c-a836-3f4c7f01ab9b

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
theorem _root_.solution {K : Type*} [CommRing K] {i : ℕ} (M : Matrix (Fin i) (Fin i) K) :
    (det (1 + (X : K[X]) • M.map C)).coeff i = M.det := by
  rw [coeff_det_one_add_X_smul_eq_sum_minors]
  have h := Finset.powersetCard_self (Finset.univ : Finset (Fin i))
  rw [Finset.card_fin] at h
  rw [h, Finset.sum_singleton]
  convert Matrix.det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)) M
    <;> rfl
end Formalism.HermitianLatticeCounting.P
