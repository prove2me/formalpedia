-- Prove2me | solution 1 for Formalism.GM.ProjS.pderiv_pow_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:10.735947+00:00
-- url     : https://prove2.me/submissions/f5a5fc06-50e2-4544-8e6c-fd03b76b8a46

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
section
variable {s : ℕ} {w e : Fin s → σ}
end
private theorem pderiv_X_pow_succ_self (v : σ) (z : ℕ) :
    pderiv v (X v ^ (z + 1) : MvPolynomial σ k) = ((z + 1 : ℕ) : MvPolynomial σ k) * X v ^ z := by
  rw [Derivation.leibniz_pow, MvPolynomial.pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul,
    Nat.add_sub_cancel]
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
section
variable {o n z : ℕ} {y : MvPolynomial σ k}
end
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
end Formalism.GM.ProjS
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (v : σ) (b : MvPolynomial σ k) (hb : pderiv v b = 0) (z : ℕ) :
    ((pderiv v).toLinearMap ^ z) (X v ^ z * b) = (z.factorial : k) • b := by
  induction z with
  | zero => simp
  | succ z ih =>
    have h1 : (pderiv v).toLinearMap (X v ^ (z + 1) * b) = ((z + 1 : ℕ) : k) • (X v ^ z * b) := by
      show pderiv v (X v ^ (z + 1) * b) = _
      rw [MvPolynomial.pderiv_mul, hb, mul_zero, add_zero, pderiv_X_pow_succ_self, MvPolynomial.smul_eq_C_mul,
        map_natCast, mul_assoc]
    rw [pow_succ, Module.End.mul_apply, h1, map_smul, ih, smul_smul, Nat.factorial_succ, Nat.cast_mul]
end Formalism.GM.ProjS
