-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_zeta_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:50:40.134884+00:00
-- url     : https://prove2.me/submissions/51b5b08f-dfc1-40c6-b885-93b19e85258a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_fvec_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} {h' : Mx k r} (hz' : h' *ᵥ z' = z')
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (g * h') = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, hz']
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
