-- Prove2me | solution 1 for Formalism.GM.F_E_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:18.531023+00:00
-- url     : https://prove2.me/submissions/cf59ba19-72d3-4815-9f85-dcd231485264

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Theorems.Thm_P2M_Formalism_GM_tieE_apply__373a5b0b31bc
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1
import Theorems.Thm_Formalism_GM_F_S_mul
import Theorems.Thm_Formalism_GM_euler_pow
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
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (hF : tieF w e u = 0) (j : ℕ) :
    tieF w e ((tieE w e ^ (j + 1)) u) = (((j + 1) * (a + b + r + j) : ℕ) : k) • (tieE w e ^ j) u := by
  induction j with
  | zero =>
    rw [tieE_pow_succ_apply 0 u, linearMap_pow_zero_apply, tieF_apply', F_S_mul hw he hwe u a b hW hE,
      ← tieF_apply' w e u, hF]
    simp only [natCast_smul_eq_natCast_mul]
    push_cast
    ring
  | succ j ih =>
    obtain ⟨h1, h2⟩ := euler_pow hw he hwe u a b hW hE (j + 1)
    rw [tieE_pow_succ_apply (j + 1) u, tieF_apply', F_S_mul hw he hwe _ _ _ h1 h2,
      ← tieF_apply' w e ((tieE w e ^ (j + 1)) u), ih, tieE_pow_succ_apply j u]
    simp only [natCast_smul_eq_natCast_mul]
    push_cast
    ring
end Formalism.GM
