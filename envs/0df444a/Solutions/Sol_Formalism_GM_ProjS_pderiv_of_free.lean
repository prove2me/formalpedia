-- Prove2me | solution 1 for Formalism.GM.ProjS.pderiv_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:56.77111+00:00
-- url     : https://prove2.me/submissions/0d9c4e7c-c2f1-4f6d-90d5-f945720fd65f

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_P2M_Formalism_GM_coeff_X_mul_pderiv__a9db2daf30da

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
private theorem coeff_pderiv_eq_coeff_add_single_mul' (v : σ) (h : MvPolynomial σ k) (m : σ →₀ ℕ) :
    coeff m (pderiv v h) = coeff (m + Finsupp.single v 1) h * ((m v : k) + 1) := by
  have h1 := Formalism.GM.coeff_X_mul_pderiv' v h (m + Finsupp.single v 1)
  rw [mul_comm (X v), MvPolynomial.coeff_mul_X] at h1
  rw [h1]
  simp
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
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}
namespace Formalism.GM.ProjS
theorem _root_.solution (v : σ) (y : MvPolynomial σ k) (h : ∀ m ∈ y.support, m v = 0) : pderiv v y = 0 := by
  ext m
  rw [coeff_pderiv_eq_coeff_add_single_mul', MvPolynomial.coeff_zero]
  have h0 : coeff (m + Finsupp.single v 1) y = 0 := by
    by_contra hne
    have h1 := h _ (MvPolynomial.mem_support_iff.mpr hne)
    simp at h1
  rw [h0, zero_mul]
end Formalism.GM.ProjS
