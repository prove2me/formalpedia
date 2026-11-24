-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:11:49.766806+00:00
-- url     : https://prove2.me/submissions/e942f220-6fa8-4819-8668-5fdff3627646

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_sub_left
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_smul_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_sub_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_wb_smul
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_wb_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_normalize
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
theorem _root_.solution {z a : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ha : inWb k r a)
    (hind : ∀ c : ℂ, a ≠ c • z) :
    ∃ e : Fin (2 * r + k + 1) → ℂ, inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      ∀ v, herm (Hpk k r) v a = 0 → herm (Hpk k r) v z = 0 → herm (Hpk k r) v e = 0 := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro h
    unfold Tz at hT
    rw [h] at hT
    simp at hT
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = herm (Hpk k r) a z / herm (Hpk k r) z z := ⟨_, rfl⟩
  have hwb : inWb k r (a - c • z) := gb_wb_sub ha (gb_wb_smul hz c)
  have hwz : herm (Hpk k r) (a - c • z) z = 0 := by
    rw [gb_sub_left, gb_smul_left, hc]
    simp [hzz]
  have hw0 : a - c • z ≠ 0 := by
    intro h
    exact hind c (sub_eq_zero.1 h)
  obtain ⟨s, hs⟩ := gb_normalize hz hT hwb hwz hw0
  refine ⟨s • (a - c • z), gb_wb_smul hwb s, ?_, hs, ?_⟩
  · rw [gb_smul_left, hwz, mul_zero]
  · intro v hva hvz
    rw [gb_smul_right, gb_sub_right, gb_smul_right, hva, hvz]
    ring
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
