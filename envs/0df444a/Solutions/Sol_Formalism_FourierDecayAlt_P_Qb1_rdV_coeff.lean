-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.rdV_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:07:59.05707+00:00
-- url     : https://prove2.me/submissions/198b936d-0b1f-4ddc-b010-f7468314522e

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qb1_hasDerivAt_orbit

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
theorem _root_.solution (hrep : IsCRepOn (UH (Hpk k r)) σ) {w : Vs} (hw : SV σ w) {X : Mx k r}
    (hX : inLie k r X) (ℓ : Vs →L[ℂ] ℂ) {g : Mx k r} (hg : g ∈ GV k r) :
    RdV X (fun x => ℓ (σ x w)) g = ℓ (σ g (dRep σ X w)) := by
  have h := (ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_orbit hrep hw hX hg)
  exact h.deriv
end Formalism.FourierDecayAlt.P.Qb1
