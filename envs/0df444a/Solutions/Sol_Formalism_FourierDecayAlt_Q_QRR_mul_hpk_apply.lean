-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.mul_hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:29:53.043876+00:00
-- url     : https://prove2.me/submissions/dd0f65eb-82f7-4199-900b-aa4ac74c0c9c

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (A : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (WeylGroupFacts.tau k r j) * WeylGroupFacts.sgn k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (WeylGroupFacts.tau k r j)]
  · congr 1
    have := j.isLt
    simp only [Hpk, WeylGroupFacts.tau, WeylGroupFacts.sgn, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ (WeylGroupFacts.tau k r j).val := fun e => hb (Fin.ext e)
    have := j.isLt
    have := b.isLt
    simp only [WeylGroupFacts.tau, Fin.val_mk] at hb'
    have h0 : Hpk k r b j = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hb' ⊢ <;> first | rfl | (exfalso; omega)
    rw [h0, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.Q.QRR
