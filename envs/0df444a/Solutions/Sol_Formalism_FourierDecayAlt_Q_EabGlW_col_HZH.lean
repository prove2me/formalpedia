-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.col_HZH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:49:26.649518+00:00
-- url     : https://prove2.me/submissions/59d387ef-d52c-4b66-baf8-f3b68d4f0b32

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
theorem _root_.solution {i : Fin (r + 1)} {Z : Mx k r} (hZ : InV k r i Z) {q : Fin (2 * r + k + 1)}
    (hq : Out k r i q) (p : Fin (2 * r + k + 1)) : (Hpk k r * Zᴴ * Hpk k r) p q = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : Out k r i b
  · have h0 : (Hpk k r * Zᴴ) p b = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro a _
      rw [Matrix.conjTranspose_apply, hZ b a (Or.inl hb), star_zero, mul_zero]
    rw [h0, zero_mul]
  · have h0 : Hpk k r b q = 0 := by
      unfold Out at hq hb
      have := i.isLt
      have := b.isLt
      have := q.isLt
      simp only [Hpk, Fin.ext_iff]
      split_ifs <;> first | rfl | omega
    rw [h0, mul_zero]
end Formalism.FourierDecayAlt.Q.EabGlW
