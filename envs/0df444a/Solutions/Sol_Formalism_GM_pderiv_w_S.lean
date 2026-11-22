-- Prove2me | solution 1 for Formalism.GM.pderiv_w_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:24.432033+00:00
-- url     : https://prove2.me/submissions/1e0294b4-7faa-476a-8ddc-5438be38633c

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_Formalism_GM_pderiv_X_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
private theorem mvPolynomial_pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  exact pderiv_X_of_ne h
end
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
namespace Formalism.GM
theorem _root_.solution (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (w c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (e c) := by
  have h0 : ∀ d, pderiv (w c) (X (e d) : MvPolynomial σ k) = 0 :=
    fun d => mvPolynomial_pderiv_X_of_ne (fun h => hwe c d h.symm)
  rw [map_sum]
  simp only [Derivation.leibniz, h0, pderiv_X_inj hw, smul_eq_mul, mul_ite, mul_one, mul_zero,
    zero_add, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end Formalism.GM
