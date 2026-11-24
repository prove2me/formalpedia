-- Prove2me | solution 1 for Formalism.GM.ProjS.eulL_pderiv_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:44.475302+00:00
-- url     : https://prove2.me/submissions/7ede2938-1e45-4502-b442-07c5c49ab5a5

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Theorems.Thm_Formalism_GM_ProjS_pderiv_comm
import Theorems.Thm_Formalism_GM_ProjS_eulL_apply
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
theorem _root_.solution {s : ℕ} (t : Fin s → σ) (v : σ) (hv : ∀ c, t c ≠ v) (h : MvPolynomial σ k) :
    eulL t (pderiv v h) = pderiv v (eulL t h) := by
  rw [eulL_apply, eulL_apply, map_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [MvPolynomial.pderiv_mul, mvPolynomial_pderiv_X_eq_zero_of_ne (hv c), zero_mul, zero_add, pderiv_comm]
end Formalism.GM.ProjS
