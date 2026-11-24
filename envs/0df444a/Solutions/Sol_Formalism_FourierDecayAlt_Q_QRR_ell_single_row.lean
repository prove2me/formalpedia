-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.ell_single_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:03:23.660176+00:00
-- url     : https://prove2.me/submissions/82265f81-f5c2-4ff3-9918-d04a24423430

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_QRR_mulVec_single__2f731049bd4a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (b : Fin (2 * r + k + 1)) (c : ℂ) :
    ell k r z (Matrix.single (eI k r l) b c) =
      if h : l.val + 1 < r then (if b = eI k r ⟨l.val + 1, h⟩ then c else 0) else c * z b := by
  unfold ell
  rw [Finset.sum_eq_single l]
  · by_cases h : l.val + 1 < r
    · rw [dif_pos h, dif_pos h, Matrix.single_apply]
      simp
    · rw [dif_neg h, dif_neg h, mulVec_single']
      simp
  · intro a' _ ha'
    have hne : eI k r l ≠ eI k r a' := fun h => ha' (Fin.ext (by
      have h' := congrArg Fin.val h
      simp only [eI] at h'
      omega))
    by_cases h : a'.val + 1 < r
    · rw [dif_pos h, Matrix.single_apply, if_neg]
      rintro ⟨h1, -⟩
      exact hne h1
    · rw [dif_neg h, mulVec_single', if_neg (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_univ l) h
end Formalism.FourierDecayAlt.Q.QRR
