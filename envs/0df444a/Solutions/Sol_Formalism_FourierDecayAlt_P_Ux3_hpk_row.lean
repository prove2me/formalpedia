-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux3.hpk_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:29:29.312439+00:00
-- url     : https://prove2.me/submissions/58add562-d715-4301-9533-0c42b7e3a614

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux3
theorem _root_.solution (k r : ℕ) (a : ℕ) (ha : a < r) (c : Fin (2 * r + k + 1)) :
    Hpk k r ⟨a, by omega⟩ c = if c = ⟨2 * r + k - a, by omega⟩ then 1 else 0 := by
  unfold Hpk
  by_cases hc : c = ⟨2 * r + k - a, by omega⟩
  · rw [if_pos hc, if_pos]
    subst hc
    refine ⟨ha, ?_⟩
    show a + (2 * r + k - a) = 2 * r + k
    omega
  · rw [if_neg hc]
    have hv : c.val ≠ 2 * r + k - a := fun h => hc (Fin.ext h)
    have e1 : ¬ ((⟨a, by omega⟩ : Fin (2 * r + k + 1)).val < r ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val + c.val = 2 * r + k) := by
      rintro ⟨_, h⟩; exact hv (by simp only at h; omega)
    have e2 : ¬ (c.val < r ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val + c.val = 2 * r + k) := by
      rintro ⟨_, h⟩; exact hv (by simp only at h; omega)
    have e3 : ¬ (r ≤ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val ∧ (⟨a, by omega⟩ : Fin (2 * r + k + 1)).val ≤ r + k ∧
        (⟨a, by omega⟩ : Fin (2 * r + k + 1)) = c) := by
      rintro ⟨h, _⟩; simp only at h; omega
    rw [if_neg e1, if_neg e2, if_neg e3]
end Formalism.FourierDecayAlt.P.Ux3
