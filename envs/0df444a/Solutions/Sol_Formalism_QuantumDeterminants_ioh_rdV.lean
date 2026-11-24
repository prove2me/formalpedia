-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ioh_rdV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:45:55.800815+00:00
-- url     : https://prove2.me/submissions/e9695fa0-3391-4ee0-8609-f4fd6fb64c56

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Theorems.Thm_Formalism_QuantumDeterminants_ioh_exp_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (P Q X x : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hQP : Q * P = 1) (hPQ : P * Q = 1) :
    RdV X f x = RdV (P * X * Q) (fun y => f (Q * y * P)) (P * x * Q) := by
  unfold RdV
  congr 1
  funext t
  have h1 : ((t : ℂ) • (P * X * Q)) = P * ((t : ℂ) • X) * Q := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1, ioh_exp_conj P Q _ hQP hPQ]
  congr 1
  have e : Q * (P * x * Q * (P * NormedSpace.exp ((t : ℂ) • X) * Q)) * P
      = (Q * P) * x * (Q * P) * NormedSpace.exp ((t : ℂ) • X) * (Q * P) := by
    simp only [Matrix.mul_assoc]
  rw [e, hQP]; simp
end Formalism.QuantumDeterminants
