-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_zeta_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:55:21.680497+00:00
-- url     : https://prove2.me/submissions/ac527db3-6a1c-49e0-8e78-940f535eeebf

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_herm_UH
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
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} {h : Mx k r} (hh : h ∈ UH (Hpk k r)) (hz : h *ᵥ z = z)
    (g : Mx k r) : zetaL k r z z' (Fin.last r) (h * g) = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  simp only [ffa_fvec_last]
  rw [← mulVec_mulVec, ← ffa_herm_UH hh (g *ᵥ z') z, hz]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
