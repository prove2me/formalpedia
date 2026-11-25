-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:17.606808+00:00
-- url     : https://prove2.me/submissions/df8df744-20ed-4650-869e-78af6a501663

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_herm

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
theorem _root_.solution {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hl : v (wI k r (Fin.last k)) = 0) :
    (herm (Hpk k r) v v).re = ∑ i, Complex.normSq (v i) := by
  rw [gb_herm hv, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · have e : i = wI k r (Fin.last k) := Fin.ext (by simp [wI, h])
    have h0 : v i = 0 := by rw [e]; exact hl
    simp [h0]
  · simp only [one_mul, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
