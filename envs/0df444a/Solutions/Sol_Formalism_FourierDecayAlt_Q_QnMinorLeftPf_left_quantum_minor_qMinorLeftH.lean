-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.QnMinorLeftPf.left_quantum_minor_qMinorLeftH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:55:35.28153+00:00
-- url     : https://prove2.me/submissions/6a93f1dd-e805-40d4-a617-51fdb60fce93

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
import Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_eabH_left
import Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_foldr_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.QnMinorLeftPf
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.QnMinorLeftPf
theorem _root_.solution : QMinorLeftH := by
  intro E _ _ n t H f a b u h
  have hT : ∀ (c : ℂ) (i j : Fin n) (g : Matrix (Fin n) (Fin n) ℂ → E),
      Formalism.QuantumDeterminants.Top (EabH H) c i j (fun x => g (h * x)) = fun x => Formalism.QuantumDeterminants.Top (EabH H) c i j g (h * x) := by
    intro c i j g
    funext x
    simp only [Formalism.QuantumDeterminants.Top]
    rw [ioLeft_eabH_left]
  funext x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [ioLeft_foldr_left h _ (fun T hTm g => ?_) f]
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hTm
  exact hT _ _ _ g
end Formalism.FourierDecayAlt.Q.QnMinorLeftPf
