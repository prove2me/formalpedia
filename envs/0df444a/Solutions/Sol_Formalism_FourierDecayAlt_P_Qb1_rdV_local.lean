-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.rdV_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:52.150897+00:00
-- url     : https://prove2.me/submissions/c554fe16-2332-43ca-9ad5-a6c571ac73aa

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
    (he : ∀ g ∈ GV k r, f g = f' g) {X : Mx k r} (hX : inLie k r X) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X f g = RdV X f' g := by
  unfold RdV
  congr 1
  funext t
  exact he _ (B5.curve_mem hg hX t)
end Formalism.FourierDecayAlt.P.Qb1
