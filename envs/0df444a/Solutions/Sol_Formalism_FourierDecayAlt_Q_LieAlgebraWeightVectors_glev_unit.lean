-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.glev_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:49:42.523786+00:00
-- url     : https://prove2.me/submissions/3b9587e9-f473-4ed0-a652-4a2244e96599

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts
import Theorems.Thm_Formalism_QuantumDeterminants_uHGroup


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
theorem _root_.solution {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) : g⁻¹ * g = 1 ∧ g * g⁻¹ = 1 := by
  obtain ⟨-, hHH, -, -⟩ := hpkFacts k r
  have hdet : IsUnit (Hpk k r).det := by
    have h := congrArg Matrix.det hHH
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact isUnit_iff_exists_inv.mpr ⟨_, h⟩
  have hu := ((uHGroup _ (Hpk k r) hdet).2.2 g hg.1).1
  exact ⟨Matrix.nonsing_inv_mul g hu, Matrix.mul_nonsing_inv g hu⟩
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
