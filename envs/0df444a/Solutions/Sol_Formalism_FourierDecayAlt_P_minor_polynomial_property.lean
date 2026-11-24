-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.minor_polynomial_property
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:49:38.597066+00:00
-- url     : https://prove2.me/submissions/0a0a1b4d-9ffd-42bf-b1b0-f917c8b92761

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Theorems.Thm_Formalism_FourierDecayAlt_P_PartialDerivativeAlgebra_pd_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_zhat_pd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MvPolynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PartialDerivativeAlgebra
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.DminPoly := by
  intro k r z z' l
  exact pd_det (fun g => (Zhat k r z z' g).submatrix (Fin.castLE (Nat.le_of_lt_succ l.isLt))
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))) (fun a b => zhat_pd k r z z' _ _)
end Formalism.FourierDecayAlt.P
