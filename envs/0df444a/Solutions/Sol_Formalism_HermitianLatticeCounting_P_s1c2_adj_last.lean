-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_adj_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:53.511528+00:00
-- url     : https://prove2.me/submissions/a9de0c99-fdc7-4464-89cc-e3470ae31d59

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_upper_last
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gh_det_upper


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (hB : IsUpperUnitriangular B) (c : Fin (r + 1)) :
    B.adjugate (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hdet : B.det = 1 := gh_det_upper hB.1 hB.2
  have h := congrFun (congrFun (Matrix.mul_adjugate B) (Fin.last r)) c
  rw [hdet, one_smul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)] at h
  · rw [hB.1, one_mul] at h
    rw [h, Matrix.one_apply]
    by_cases hc : c = Fin.last r
    · simp [hc]
    · simp [hc, Ne.symm hc]
  · intro d _ hd; rw [s1c2_upper_last B hB, if_neg hd, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'
end Formalism.HermitianLatticeCounting.P
