-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_GG_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:17:33.855159+00:00
-- url     : https://prove2.me/submissions/e481ea69-e4c8-4c5c-b9c0-9b398261107c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_fvec_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp


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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ∞ (fun x : Mx k r => (GGl k r z z' x : ℂ)) := by
  have hζ : ContDiff ℝ ∞ (fun x : Mx k r => zetaL k r z z' (Fin.last r) x) := by
    have h1 := (LinearMap.toContinuousLinearMap (ffaZetaLin z z')).contDiff (n := ∞)
    convert h1 using 1
    funext x
    simp only [zetaL, ffa_fvec_last]
    rfl
  have hc : ContDiff ℝ ∞ (fun x : Mx k r => Complex.conjCLE (zetaL k r z z' (Fin.last r) x)) :=
    Complex.conjCLE.contDiff.comp hζ
  have he : (fun x : Mx k r => (GGl k r z z' x : ℂ)) = fun x =>
      zetaL k r z z' (Fin.last r) x * Complex.conjCLE (zetaL k r z z' (Fin.last r) x) -
        (Tz k r z : ℂ) * (Tz k r z' : ℂ) := by
    funext x
    simp [GGl, Complex.mul_conj]
  rw [he]
  exact (hζ.mul hc).sub contDiff_const
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
