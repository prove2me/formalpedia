-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.idx_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:22:50.043918+00:00
-- url     : https://prove2.me/submissions/eebbcd29-b7b2-4662-890e-5a576e8ff149

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_ord
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
open Formalism.FourierDecayAlt.M
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution (P : M.Par) (hP : P.OK) (π π' : M.Ty P) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (h : M.rho P π i = M.rho P π' j) : i = j := by
  have hI := Mx3.tyInterlaces P hP π
  have hI' := Mx3.tyInterlaces P hP π'
  rcases lt_trichotomy i j with hij | hij | hij
  · have o := (Mx3.ord P.k P.u P.u' (M.rho P π') hI' i hi).2.2.2 j hj hij
    have b := hI i hi
    linarith [o.1, b.2.2.1]
  · exact hij
  · have o := (Mx3.ord P.k P.u P.u' (M.rho P π) hI j hj).2.2.2 i hi hij
    have b := hI' j hj
    linarith [o.1, b.2.2.1]
end Formalism.FourierDecayAlt.P.NFx2
