-- Prove2me | solution 1 for Formalism.GM.euler_e_S_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:11.119643+00:00
-- url     : https://prove2.me/submissions/d0039b8d-00ea-4192-a34e-d71e25b42e18

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_Formalism_GM_pderiv_e_S
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
theorem _root_.solution (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (b : ℕ) (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) :
    ∑ c, X (e c) * pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      ((b + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by
  have h1 : ∀ c, X (e c) * pderiv (e c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * X (e c) * g + (∑ d, X (w d) * X (e d)) * (X (e c) * pderiv (e c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_e_S he hwe, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hE]
  simp only [natCast_smul_eq_natCast_mul]
  push_cast
  ring
end Formalism.GM
