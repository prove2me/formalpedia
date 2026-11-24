-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ge_det_mul_eq_sum_principal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:42.930152+00:00
-- url     : https://prove2.me/submissions/553e010a-a34e-45cd-b32a-e4110764e804

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_ge_coeff_top_det

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
    (A * B).det = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ((B * A).submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
  rw [← ge_coeff_top_det (A * B)]
  have h1 : (1 : Matrix (Fin i) (Fin i) K[X]) + (X : K[X]) • (A * B).map C
      = 1 + ((X : K[X]) • A.map C) * (B.map C) := by
    rw [Matrix.map_mul, Matrix.smul_mul]
  have h2 : (B.map C) * ((X : K[X]) • A.map C) = (X : K[X]) • (B * A).map C := by
    rw [Matrix.mul_smul]; congr 1; simp [Matrix.map_mul]
  rw [h1, det_one_add_mul_comm, h2, coeff_det_one_add_X_smul_eq_sum_minors]
end Formalism.HermitianLatticeCounting.P
