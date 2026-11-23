-- Prove2me | solution 1 for Formalism.GM.F_S_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:54.717218+00:00
-- url     : https://prove2.me/submissions/d1ad9b9c-8200-49fc-9873-def595d35fae

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_Formalism_GM_pderiv_e_S
import Theorems.Thm_Formalism_GM_pderiv_w_S
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
private theorem mvPolynomial_pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ k) = 1 := by
  exact pderiv_X_self i
private theorem natCast_smul_eq_natCast_mul (n : ℕ) (g : MvPolynomial σ k) :
    (n : k) • g = (n : MvPolynomial σ k) * g := by
  rw [smul_eq_C_mul, map_natCast]
end
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
namespace Formalism.GM
theorem _root_.solution (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g)) =
      (∑ d, X (w d) * X (e d)) * ∑ c, pderiv (w c) (pderiv (e c) g) + ((a + b + r : ℕ) : k) • g := by
  have h1 : ∀ c, pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * g + (∑ d, X (w d) * X (e d)) * pderiv (e c) g := by
    intro c
    rw [Derivation.leibniz, pderiv_e_S he hwe, smul_eq_mul, smul_eq_mul]
    ring
  have h2 : ∀ c, pderiv (w c) (X (w c) * g) = g + X (w c) * pderiv (w c) g := by
    intro c
    rw [Derivation.leibniz, mvPolynomial_pderiv_X_self, smul_eq_mul, smul_eq_mul]
    ring
  have h3 : ∀ c, pderiv (w c) ((∑ d, X (w d) * X (e d)) * pderiv (e c) g) =
      X (e c) * pderiv (e c) g + (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_w_S hw hwe, smul_eq_mul, smul_eq_mul]
    ring
  calc ∑ c, pderiv (w c) (pderiv (e c) ((∑ d, X (w d) * X (e d)) * g))
      = ∑ c, (g + (X (w c) * pderiv (w c) g + X (e c) * pderiv (e c) g) +
          (∑ d, X (w d) * X (e d)) * pderiv (w c) (pderiv (e c) g)) := by
        refine Finset.sum_congr rfl (fun c _ => ?_)
        rw [h1, map_add, h2, h3]
        ring
    _ = (∑ _c : Fin r, g) + ((∑ c, X (w c) * pderiv (w c) g) + ∑ c, X (e c) * pderiv (e c) g) +
          (∑ d, X (w d) * X (e d)) * ∑ c, pderiv (w c) (pderiv (e c) g) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
        rw [hW, hE]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, natCast_smul_eq_natCast_mul]
        push_cast
        ring
end Formalism.GM
