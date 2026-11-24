-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.hpk_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:29:00.581803+00:00
-- url     : https://prove2.me/submissions/8093ef34-40b8-4c9a-8d1d-59cea933893b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ l : Fin (2 * r + k + 1),
      l.val ≠ (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) →
      Hpk k r i l = 0 := by
    intro l hl
    have hl' := l.isLt
    unfold Hpk
    simp only [Fin.ext_iff]
    split_ifs at hl ⊢ <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_eq_single_of_mem
    ⟨(if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val), by split_ifs <;> omega⟩
    (Finset.mem_univ _)]
  · unfold Hpk
    simp only [Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro l _ hl
    rw [key l (fun h => hl (Fin.ext h)), MulZeroClass.zero_mul]
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution : IsUnit (Hpk k r) := by
  exact ⟨⟨Hpk k r, Hpk k r, hpk_sq_lemma, hpk_sq_lemma⟩, rfl⟩
end Formalism.FourierDecayAlt.P.B4
