-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.lieL_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:59.060553+00:00
-- url     : https://prove2.me/submissions/084d09f5-795e-4dde-8095-78a87af18cf1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} {X : Mx k r} (hX : X ∈ LieL k r i) (t : ℝ) :
    (t : ℂ) • X ∈ LieL k r i := by
  obtain ⟨h1, h2⟩ := hX
  have h1' : Xᴴ * Hpk k r + Hpk k r * X = 0 := h1
  refine ⟨?_, fun a ha => ?_⟩
  · show ((t : ℂ) • X)ᴴ * Hpk k r + Hpk k r * ((t : ℂ) • X) = 0
    rw [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, ← smul_add, h1', smul_zero]
  · obtain ⟨e1, e2⟩ := h2 a ha
    exact ⟨by rw [Matrix.smul_mulVec, e1, smul_zero],
      by rw [Matrix.smul_mulVec, e2, smul_zero]⟩
end Formalism.FourierDecayAlt.Q.EabGlW
