-- Prove2me | solution 1 for Formalism.GM.F_pow_E_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:09.45102+00:00
-- url     : https://prove2.me/submissions/9d08fb09-f3e7-4fd7-bf57-22f3ac7e335f

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_Formalism_GM_F_E_pow
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
private theorem linearMap_pow_succ_apply_eq_pow_apply (f : MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (n : ℕ)
    (x : MvPolynomial σ k) : (f ^ (n + 1)) x = (f ^ n) (f x) := by
  rw [pow_succ]; first | done | rfl
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
    (u : MvPolynomial σ k) (a b N0 : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (hF : tieF w e u = 0) (hN : a + b + r = N0 + 1)
    (j l : ℕ) :
    (tieF w e ^ j) ((tieE w e ^ l) u) =
      ((l.descFactorial j * (N0 + l).descFactorial j : ℕ) : k) • (tieE w e ^ (l - j)) u := by
  induction j generalizing l with
  | zero =>
    simp only [linearMap_pow_zero_apply, Nat.descFactorial_zero, mul_one, Nat.cast_one, one_smul, Nat.sub_zero]
  | succ j ih =>
    cases l with
    | zero =>
      rw [linearMap_pow_succ_apply_eq_pow_apply, linearMap_pow_zero_apply, hF, map_zero, Nat.zero_descFactorial_succ, zero_mul,
        Nat.cast_zero, zero_smul]
    | succ l =>
      rw [linearMap_pow_succ_apply_eq_pow_apply, F_E_pow hw he hwe u a b hW hE hF l, map_smul, ih l, smul_smul,
        ← Nat.cast_mul, Nat.add_sub_add_right]
      congr 2
      rw [hN, Nat.succ_descFactorial_succ, show N0 + (l + 1) = N0 + l + 1 by omega, Nat.succ_descFactorial_succ]
      ring
end Formalism.GM
