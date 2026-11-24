-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_normalize
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:55.7108+00:00
-- url     : https://prove2.me/submissions/9fbc2ab9-e560-49fe-ba7b-5ddb69c85a63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_symm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


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
theorem _root_.solution {b v : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) (hv : inWb k r v)
    (hvb : herm (Hpk k r) v b = 0) (hv0 : v ≠ 0) : ∃ s : ℂ, herm (Hpk k r) (s • v) (s • v) = 1 := by
  have hp := gb_pos hb hT hv hvb hv0
  have him : (herm (Hpk k r) v v).im = 0 := by
    have h := congrArg Complex.im (gb_symm hv hv)
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  set q := (herm (Hpk k r) v v).re with hq
  have hvv : herm (Hpk k r) v v = (q : ℂ) := Complex.ext (by simp [hq]) (by simp [him])
  refine ⟨(((Real.sqrt q)⁻¹ : ℝ) : ℂ), ?_⟩
  rw [gb_smul_left, gb_smul_right, hvv]
  have hst : star (((Real.sqrt q)⁻¹ : ℝ) : ℂ) = (((Real.sqrt q)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [hst]
  have hne : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hr : ((Real.sqrt q)⁻¹ * ((Real.sqrt q)⁻¹ * q) : ℝ) = 1 := by
    field_simp
    linarith [Real.mul_self_sqrt hp.le, Real.sq_sqrt hp.le]
  exact_mod_cast hr
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
