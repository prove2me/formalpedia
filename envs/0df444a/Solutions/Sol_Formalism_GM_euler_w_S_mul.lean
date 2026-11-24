-- Prove2me | solution 1 for Formalism.GM.euler_w_S_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:00.819382+00:00
-- url     : https://prove2.me/submissions/0a7b9814-0680-45f7-841a-e298b9b86d80

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
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
theorem _root_.solution (hw : Function.Injective w) (hwe : ∀ c d, w c ≠ e d)
    (g : MvPolynomial σ k) (a : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g) :
    ∑ c, X (w c) * pderiv (w c) ((∑ d, X (w d) * X (e d)) * g) =
      ((a + 1 : ℕ) : k) • ((∑ d, X (w d) * X (e d)) * g) := by
  have h1 : ∀ c, X (w c) * pderiv (w c) ((∑ d, X (w d) * X (e d)) * g) =
      X (w c) * X (e c) * g + (∑ d, X (w d) * X (e d)) * (X (w c) * pderiv (w c) g) := by
    intro c
    rw [Derivation.leibniz, pderiv_w_S hw hwe, smul_eq_mul, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun c _ => h1 c), Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hW]
  simp only [natCast_smul_eq_natCast_mul]
  push_cast
  ring
end Formalism.GM
