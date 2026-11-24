-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.lc_miss
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:57.786181+00:00
-- url     : https://prove2.me/submissions/f129069e-e714-4ee6-9a85-c48073200f43

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_posL_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (l₀ : Fin t) (h : ∀ l, a l ≠ b l₀) :
    lc k r i a b = 0 := by
  unfold lc
  exact Finset.sum_eq_zero fun σ _ => by
    rw [Finset.prod_eq_zero (Finset.mem_univ l₀) (if_neg fun e => h (σ l₀) (posL_inj i e)), mul_zero]
end Formalism.FourierDecayAlt.P.Qx2
