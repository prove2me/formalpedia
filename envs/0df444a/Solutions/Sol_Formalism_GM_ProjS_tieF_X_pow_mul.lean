-- Prove2me | solution 1 for Formalism.GM.ProjS.tieF_X_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:12.542086+00:00
-- url     : https://prove2.me/submissions/4374b9e6-34b4-48f7-ab2e-2b531e0a1683

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_P2M_Formalism_GM_tieF_apply__aa4421b36bb1

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
private theorem mvPolynomial_pderiv_X_eq_zero_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  classical
  rw [MvPolynomial.pderiv_X, Pi.single_apply, if_neg h]
private theorem pderiv_X_pow_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) : pderiv i (X j ^ z : MvPolynomial σ k) = 0 := by
  rw [Derivation.leibniz_pow, mvPolynomial_pderiv_X_eq_zero_of_ne h, smul_zero, smul_zero]
private theorem pderiv_X_pow_mul_of_ne {i j : σ} (h : j ≠ i) (z : ℕ) (g : MvPolynomial σ k) :
    pderiv i (X j ^ z * g) = X j ^ z * pderiv i g := by
  rw [MvPolynomial.pderiv_mul, pderiv_X_pow_of_ne h, zero_mul, zero_add]
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
theorem _root_.solution {r : ℕ} (w e : Fin r → σ) (zv : σ) (hz : ∀ c, w c ≠ zv ∧ e c ≠ zv) (z : ℕ)
    (g : MvPolynomial σ k) : tieF w e (X zv ^ z * g) = X zv ^ z * tieF w e g := by
  simp only [Formalism.GM.tieF_apply', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_X_pow_mul_of_ne (hz c).2.symm, pderiv_X_pow_mul_of_ne (hz c).1.symm]
end Formalism.GM.ProjS
