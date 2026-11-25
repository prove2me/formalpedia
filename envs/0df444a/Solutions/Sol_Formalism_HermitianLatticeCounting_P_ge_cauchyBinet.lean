-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ge_cauchyBinet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:41.265626+00:00
-- url     : https://prove2.me/submissions/fa20b428-efee-43f6-9f91-4105d4725a69

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ge_det_mul_eq_sum_principal
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ge_principal_minor_factor

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
    (B : Matrix (Fin n) (Fin i) K) :
    (A * B).det = ∑ I : {I : Finset (Fin n) // I.card = i},
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det * (A.submatrix id (I.1.orderEmbOfFin I.2)).det := by
  rw [ge_det_mul_eq_sum_principal]
  rw [Finset.sum_subtype (p := fun I : Finset (Fin n) => I.card = i) _ (by intro I; simp)]
  exact Finset.sum_congr rfl fun I _ => ge_principal_minor_factor A B I.1 I.2
end Formalism.HermitianLatticeCounting.P
