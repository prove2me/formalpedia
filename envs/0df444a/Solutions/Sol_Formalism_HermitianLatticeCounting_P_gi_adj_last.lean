-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gi_adj_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:43.631704+00:00
-- url     : https://prove2.me/submissions/f9dd8933-33d2-4057-bb44-57832755f991

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gi_lead_eq

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
theorem _root_.solution {R : Type*} [CommRing R] (r : ℕ) (M : Matrix (Fin (r + 1)) (Fin (r + 1)) R) :
    M.adjugate (Fin.last r) (Fin.last r) = leadingPrincipalMinor M r := by
  rw [gi_lead_eq, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, Fin.val_last,
    Even.neg_one_pow ⟨r, rfl⟩, one_mul]
end Formalism.HermitianLatticeCounting.P
