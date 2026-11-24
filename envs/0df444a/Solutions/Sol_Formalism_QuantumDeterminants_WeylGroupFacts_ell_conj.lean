-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WeylGroupFacts.ell_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:43.964889+00:00
-- url     : https://prove2.me/submissions/5ea43ff5-fef5-4d96-8b6e-1daedaa8625f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mul_apply_of_row
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mul_apply_of_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mulVec_apply_of_row

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) :
    ell k r z (h * g * h') = ell k r z g := by
  unfold block at hh hh'
  unfold ell
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 (eI k r a) p (Or.inl a.isLt)
  by_cases h1 : a.val + 1 < r
  · simp only [dif_pos h1]
    rw [mul_assoc, mul_apply_of_row _ _ _ hrow]
    exact mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (Or.inl h1))
  · simp only [dif_neg h1]
    rw [mul_assoc, ← Matrix.mulVec_mulVec, mulVec_apply_of_row _ _ hrow, ← Matrix.mulVec_mulVec, hz]
end Formalism.QuantumDeterminants.WeylGroupFacts
