-- Prove2me | solution 1 for Formalism.GM.euler_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:10.595337+00:00
-- url     : https://prove2.me/submissions/d8d4402c-0445-495d-a0ec-80cc694c24da

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc
import Theorems.Thm_Formalism_GM_euler_w_S_mul
import Theorems.Thm_Formalism_GM_euler_e_S_mul
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
private theorem linearMap_pow_zero_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (x : MvPolynomial σ k) :
    (f ^ 0) x = x := by
  rw [pow_zero]; first | done | rfl
private theorem linearMap_pow_succ_apply_eq_apply_pow (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (n : ℕ)
    (x : MvPolynomial σ k) : (f ^ (n + 1)) x = f ((f ^ n) x) := by
  rw [pow_succ']; first | done | rfl
private theorem tieE_pow_succ_apply (j : ℕ) (x : MvPolynomial σ k) :
    (tieE w e ^ (j + 1)) x = (∑ d, X (w d) * X (e d)) * (tieE w e ^ j) x := by
  rw [linearMap_pow_succ_apply_eq_apply_pow, tieE_apply']
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
    (u : MvPolynomial σ k) (a b : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (j : ℕ) :
    (∑ c, X (w c) * pderiv (w c) ((tieE w e ^ j) u) = ((a + j : ℕ) : k) • (tieE w e ^ j) u) ∧
    (∑ c, X (e c) * pderiv (e c) ((tieE w e ^ j) u) = ((b + j : ℕ) : k) • (tieE w e ^ j) u) := by
  induction j with
  | zero =>
    simp only [linearMap_pow_zero_apply, Nat.add_zero]
    exact ⟨hW, hE⟩
  | succ j ih =>
    rw [tieE_pow_succ_apply j u]
    refine ⟨?_, ?_⟩
    · rw [euler_w_S_mul hw hwe _ _ ih.1, Nat.add_assoc]
    · rw [euler_e_S_mul he hwe _ _ ih.2, Nat.add_assoc]
end Formalism.GM
