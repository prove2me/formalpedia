-- Prove2me | solution 1 for Formalism.GM.pderiv_e_S
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:21.145121+00:00
-- url     : https://prove2.me/submissions/fd551860-ebac-4866-87b0-ba6cc87321e4

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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (c : Fin r) : pderiv (e c) (∑ d, X (w d) * X (e d) : MvPolynomial σ k) = X (w c) := by
  have h0 : ∀ d, pderiv (e c) (X (w d) : MvPolynomial σ k) = 0 := fun d => mvPolynomial_pderiv_X_of_ne (hwe d c)
  rw [map_sum]
  simp only [Derivation.leibniz, h0, pderiv_X_inj he, smul_eq_mul, mul_ite, mul_one, mul_zero,
    add_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
end Formalism.GM
