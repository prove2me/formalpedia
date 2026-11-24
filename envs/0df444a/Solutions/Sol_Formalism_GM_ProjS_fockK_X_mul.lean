-- Prove2me | solution 1 for Formalism.GM.ProjS.fockK_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:33.124805+00:00
-- url     : https://prove2.me/submissions/ecc9444c-e884-4e98-900b-8abaca3db6ec

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_fockK_eq
import Theorems.Thm_Formalism_GM_ProjS_mfac_add_single
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
variable {k σ : Type} [Field k]
namespace Formalism.GM.ProjS
theorem _root_.solution (v : σ) (g h : MvPolynomial σ k) :
    M.fockK (X v * g) h = M.fockK g (pderiv v h) := by
  rw [fockK_eq, fockK_eq, mul_comm (X v) g, MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [addRightEmbedding_apply, MvPolynomial.coeff_mul_X, coeff_pderiv_eq_coeff_add_single_mul', mfac_add_single]
  ring
end Formalism.GM.ProjS
