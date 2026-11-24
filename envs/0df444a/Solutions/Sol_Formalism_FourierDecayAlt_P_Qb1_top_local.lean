-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.top_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:03.380848+00:00
-- url     : https://prove2.me/submissions/01501021-e99b-433b-8ebb-b36858acc88c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_lie2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_rdV_local

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
variable {σ : Mx k r → (Vs →L[ℂ] Vs)}
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (c : ℂ) (a b : Fin (2 * r + k + 1)) {g : Mx k r} (hg : g ∈ GV k r) :
    QuantumDeterminants.Top (EH k r) c a b f g = QuantumDeterminants.Top (EH k r) c a b f' g := by
  unfold QuantumDeterminants.Top
  simp only [EH, EabH]
  rw [he g hg, rdV_local he (lie1 _) hg, rdV_local he (lie2 _) hg]
end Formalism.FourierDecayAlt.P.Qb1
