-- Prove2me | solution 1 for Formalism.ELL.MultiplicativeWeight.W_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:07.462505+00:00
-- url     : https://prove2.me/submissions/a466973f-2cd9-461d-8003-87bdc95a5705

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_CompExpWeight
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CompExp
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_one
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_mul
import Theorems.Thm_Formalism_ELL_MultiplicativeWeight_W_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries IsUltrametricDist
universe u
open Formalism Formalism.ELL Formalism.ELL.MultiplicativeWeight
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type} (c : ℝ)
variable {c}
namespace Formalism.ELL.MultiplicativeWeight
theorem _root_.solution (hc : 0 < c) (hc1 : c ≤ 1) (a : σ → MvPowerSeries σ K) (ha : ∀ i, W c 1 (a i))
    (d : σ →₀ ℕ) : W c (d.degree : ℤ) (d.prod fun s n => a s ^ n) := by
  classical
  unfold Finsupp.prod
  have hdeg : (d.degree : ℤ) = ∑ s ∈ d.support, ((d s : ℕ) : ℤ) := by
    show (((∑ i ∈ d.support, d i : ℕ)) : ℤ) = _
    push_cast; rfl
  rw [hdeg]
  induction d.support using Finset.induction_on with
  | empty => simpa using W_one hc hc1
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.sum_insert hs]
    have := W_pow hc hc1 (ha s) (d s)
    rw [mul_one] at this
    exact W_mul hc this ih
end Formalism.ELL.MultiplicativeWeight
