-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.lc_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:39:29.897898+00:00
-- url     : https://prove2.me/submissions/9205977a-a6b4-40f4-a029-8134771c54bc

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_posL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at

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
theorem _root_.solution {t : ℕ} (a : Fin t → Fin (mdim k r i)) (ha : Function.Injective a) : lc k r i a a = 1 := by
  unfold lc
  rw [Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    obtain ⟨l, hl⟩ : ∃ l, σ l ≠ l := by
      by_contra hc
      push_neg at hc
      exact hσ (Equiv.ext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (if_neg fun e => hl (ha (posL_inj i e))), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.Qx2
