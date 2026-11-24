-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QRR.dag_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:49.87848+00:00
-- url     : https://prove2.me/submissions/f8511ba6-c082-42a4-a6ca-d58e264339f2

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_PatEntryZero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_hpk_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_QRR_mul_hpk_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
private lemma hpk_mul_lemma (A : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * A) i j = WeylGroupFacts.sgn k r i * A (WeylGroupFacts.tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (WeylGroupFacts.tau k r i)]
  · congr 1
    have := i.isLt
    simp only [Hpk, WeylGroupFacts.tau, WeylGroupFacts.sgn, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ (WeylGroupFacts.tau k r i).val := fun e => hb (Fin.ext e)
    have := i.isLt
    have := b.isLt
    simp only [WeylGroupFacts.tau, Fin.val_mk] at hb'
    have h0 : Hpk k r i b = 0 := by
      simp only [Hpk, Fin.ext_iff]
      split_ifs at hb' ⊢ <;> first | rfl | (exfalso; omega)
    rw [h0, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.Q.QRR
end
end

set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QRR
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.QRR
theorem _root_.solution (Z : Mx k r) (i j : Fin (2 * r + k + 1)) :
    dag k r Z i j = WeylGroupFacts.sgn k r i * star (Z (WeylGroupFacts.tau k r j) (WeylGroupFacts.tau k r i)) * WeylGroupFacts.sgn k r j := by
  unfold dag
  rw [hpk_inv, mul_hpk_apply, hpk_mul_lemma, Matrix.conjTranspose_apply]
end Formalism.FourierDecayAlt.Q.QRR
