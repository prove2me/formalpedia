-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.sum_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:25.108805+00:00
-- url     : https://prove2.me/submissions/0498e8f0-8d45-4fc1-884a-df4a9d84dc76

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (μ : Fin (N + 1) × Fin r →₀ ℕ) (hμ : MultiDeg LL μ) :
    (∑ v : Fin (N + 1) × Fin r, μ v • dv v.1) = (LL.snoc LL.total).deg := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dv, Pi.add_apply, mul_add, sum_add_distrib]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  induction k using Fin.lastCases with
  | last =>
    have hne : ∀ x : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc x :=
      fun x h => Fin.castSucc_ne_last x h.symm
    simp only [Pi.single_apply, hne, if_false, mul_zero, sum_const_zero, zero_add,
      if_true, mul_one]
    simp only [Letters.snoc, Fin.lastCases_last, Letters.total]
    exact sum_congr rfl (fun i _ => hμ i)
  | cast k =>
    simp only [Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last k, if_false, mul_zero,
      sum_const_zero, add_zero]
    simp only [Letters.snoc, Fin.lastCases_castSucc]
    rw [Finset.sum_eq_single k]
    · simp only [if_true, mul_one]; exact hμ k
    · intro b _ hb; simp [Ne.symm hb]
    · simp
end Formalism.GM.gammaIntegralityLemmas
