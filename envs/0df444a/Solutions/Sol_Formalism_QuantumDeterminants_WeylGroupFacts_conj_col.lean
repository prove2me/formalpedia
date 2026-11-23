-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.conj_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:05.205127+00:00
-- url     : https://prove2.me/submissions/73cdc2ed-3053-4bd4-9bba-ee90b8d1f580

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_block_mul_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WeylGroupFacts
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.WeylGroupFacts
theorem _root_.solution {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') := by
  unfold block at hh hh'
  intro i j hj hij
  have key : ∀ p, (h * g) i p * h' p j = h i p * h' p j := by
    intro p
    by_cases hpj : p = j
    · rw [hpj, block_mul_col (by unfold block; exact hh) hg i j hj hij]
    · by_cases hjm : j.val < r
      · rw [hh'.1 p j (Or.inl hjm), if_neg hpj, mul_zero, mul_zero]
      · by_cases hpm : p.val < r ∨ r + k < p.val
        · rw [hh'.2 p j hpm, if_neg hpj, mul_zero, mul_zero]
        · rw [block_mul_col (by unfold block; exact hh) hg i p (by omega) (Or.inr (by omega))]
  have e : (h * g * h') i j = (h * h') i j := by
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun p _ => key p)
  rw [e, hinv, Matrix.one_apply]
end Formalism.QuantumDeterminants.WeylGroupFacts
