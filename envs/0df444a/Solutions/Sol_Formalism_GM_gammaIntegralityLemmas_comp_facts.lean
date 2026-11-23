-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.comp_facts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:26.649427+00:00
-- url     : https://prove2.me/submissions/91a14575-771a-4a76-a5fa-705b0ad34488

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
theorem _root_.solution (LL : Letters (N + 1)) (b : ℕ) (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) (c0 c1 : ℕ)
    (hd : δv δ + Pi.single (Fin.castSucc (Fin.last N)) c0 + Pi.single (Fin.last (N + 1)) c1 + b • eWY =
      (LL.snoc LL.total).deg) :
    (∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k)) ∧
    δv δ (Fin.castSucc (Fin.last N)) + c0 + b = LL.deg (Fin.last N) ∧
    δv δ (Fin.last (N + 1)) + c1 + b = LL.total := by
  have hne : ∀ k : Fin (N + 1), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc k :=
    fun k h => Fin.castSucc_ne_last k h.symm
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have := congrFun hd (Fin.castSucc (Fin.castSucc k))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, Fin.castSucc_inj, Fin.castSucc_ne_last,
      if_false, add_zero, smul_eq_mul, mul_zero, Letters.snoc, Fin.lastCases_castSucc] at this
    exact this
  · have := congrFun hd (Fin.castSucc (Fin.last N))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, Fin.castSucc_ne_last, if_true, if_false,
      add_zero, smul_eq_mul, mul_one, Letters.snoc, Fin.lastCases_castSucc] at this
    omega
  · have := congrFun hd (Fin.last (N + 1))
    simp only [Pi.add_apply, Pi.smul_apply, eWY, Pi.single_apply, hne, if_true, if_false,
      zero_add, smul_eq_mul, mul_one, Letters.snoc, Fin.lastCases_last] at this
    omega
end Formalism.GM.gammaIntegralityLemmas
