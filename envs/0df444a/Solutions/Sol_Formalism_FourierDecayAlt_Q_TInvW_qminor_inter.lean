-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.qminor_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:58:45.494982+00:00
-- url     : https://prove2.me/submissions/b7143430-52d9-40f8-add2-2a7bbc8fffd9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_prod_inter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, E a b * R = R * E' a b)
    {t : ℕ} (α β : Fin t → Fin n) (u : ℂ) : qminor E α β u * R = R * qminor E' α β u := by
  have key : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α (σ k)) (β k)).prod * R =
        R * (List.ofFn fun k : Fin t => Tm E' (u - (k : ℂ)) (α (σ k)) (β k)).prod := by
    intro σ
    have hl := prod_inter E E' R h (List.ofFn fun k : Fin t => (u - (k : ℂ), α (σ k), β k))
    simpa [List.map_ofFn, Function.comp_def] using hl
  unfold qminor
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_assoc, key σ, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ R).eq]
end Formalism.FourierDecayAlt.Q.TInvW
