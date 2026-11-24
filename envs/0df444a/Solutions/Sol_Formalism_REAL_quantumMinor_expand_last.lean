-- Prove2me | solution 1 for Formalism.REAL.quantumMinor_expand_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:59.455063+00:00
-- url     : https://prove2.me/submissions/e2acd98f-dad8-4159-a63f-1d8651799c07

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_sign_cycleToLast
import Theorems.Thm_Formalism_REAL_extendLast_castSucc
import Theorems.Thm_Formalism_REAL_extendLast_last
import Theorems.Thm_Formalism_REAL_sign_extendLast
import Theorems.Thm_Formalism_REAL_lastColumnSplit_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m - (j : ℕ)) : ℤ) : A) *
      qminor E (a ∘ Fin.succAbove j) (b ∘ Fin.castSucc) u * Tm E (u - (m : ℂ)) (a j) (b (Fin.last m)) := by
  unfold qminor
  rw [← (Equiv.ofBijective _ (lastColumnSplit_bijective m)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  simp only [Equiv.ofBijective_apply, lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_mul,
    List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
    Equiv.Perm.mul_apply, extendLast_castSucc, cycleToLast_castSucc, extendLast_last, cycleToLast_last,
    Fin.val_castSucc, Fin.val_last, Function.comp_apply, mul_assoc]
end Formalism.REAL
